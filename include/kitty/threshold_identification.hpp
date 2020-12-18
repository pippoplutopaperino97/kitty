/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
  \file threshold_identification.hpp
  \brief Threshold logic function identification

  \author CS-472 2020 Fall students
*/

#pragma once

#include <vector>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "traits.hpp"
#include "isop.hpp"
#include "operations.hpp"
#include "cube.hpp"
#include "static_truth_table.hpp"
#include "dynamic_truth_table.hpp"

namespace kitty
{

/*! \brief Threshold logic function identification

  Given a truth table, this function determines whether it is a threshold logic function (TF)
  and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

  f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

  where w_i are the weight values and T is the threshold value.
  The linear form of a TF is the vector [w_1, ..., w_n; T].

  \param tt The truth table
  \param plf Pointer to a vector that will hold a linear form of `tt` if it is a TF.
             The linear form has `tt.num_vars()` weight values and the threshold value
             in the end.
  \return `true` if `tt` is a TF; `false` if `tt` is a non-TF.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold( const TT& tt, std::vector<int64_t>* plf = nullptr )
{
  std::vector<int64_t> linear_form;

  /* TODO */
  //variables initialization and check for the unateness of the function
  auto num_vars = tt.num_vars(); //number of variables involved in the function
  //auto bits = tt.num_bits(); //the truth table
  auto tt_flip = tt;
  std::vector<bool> builder; //helping vector for the reconstruction of the vector linear_form
  for (auto i = 0u; i < num_vars; ++i)
  {
    auto pos_cofactor = cofactor1(tt, i);
    auto neg_cofactor = cofactor0(tt, i);
    auto pos_unate = implies(neg_cofactor, pos_cofactor);
    auto neg_unate = implies(pos_cofactor, neg_cofactor);
    if ((pos_unate || neg_unate) == false) //the function is binate
    {
      /* if tt is non-TF: */
      std::cout << "Since the function is binate in variable " << i <<", we conclude immediately that it is a non-TF" << std::endl;
      return false;
    }
    else
    {
      if (neg_unate == true)
      {
        //std::cout << "The function is neg unate in var " << i << std::endl;
        tt_flip = flip(tt_flip,i);
        builder[i] = builder.emplace_back(false); //to remember that flipping occurred
      }
      else
      {
        //std::cout << "The function is pos unate in var " << i << std::endl;
        builder[i] = builder.emplace_back(true); //to remember that no flipping occurred
      }
    }
  }


  //definition of ON-set and OFF-set for lp algorithm
  std::vector<cube> on_set = isop(tt_flip); //a cube is built from an equivalent string in cube.hpp and isop gives its minterms
  std::vector<cube> off_set = isop(unary_not(tt_flip));

  //lp algorithm
  lprec *lp;
  int Ncol, * column = nullptr, j;
  bool check = true; //a check that allows to go further with the algorithm only if no errors are present
  REAL *row = nullptr;

  Ncol = num_vars + 1; //# of columns = #variables + 1 to count T
  lp = make_lp(0, Ncol); //lp for first row

  if(lp == nullptr)
    check = false; /* couldn't construct a new model... */

  if(check) {
    /* create space large enough for one row */
    column = (int *) malloc(Ncol * sizeof(*column));
    row = (REAL *) malloc(Ncol * sizeof(*row));

    if((column == nullptr) || (row == nullptr))
      check = false;
  }

  set_add_rowmode(lp, TRUE);  /* makes building the model faster if it is done rows by row */

  if(check)
  {
    //constraints for the ON-SET
    for (cube cube : on_set)
    {
      j = 0;
      for (int i = 0; i < Ncol - 1; ++i) //-1 because the column for T will be created apart
      {
        if (cube.get_mask(i)) //when the variable i belongs to the ON-set cube add 1 as weight factor
        {
          column[j] = i + 1; //the number of columns starts from 1
          row[j] = 1;        //the weight is 1 when present, otherwise it is 0
          ++j;
          //std::cout << "The variable " << i << " is included in the " << i+1 <<" column" << std::endl;
        }
        else //when the variable i does not belong to the ON-set cube add 0 as weight factor
        {
          column[j] = i + 1; //the number of columns starts from 1
          row[j] = 0;        //the weight is 1 when present, otherwise it is 0
          ++j;
          //std::cout << "The variable " << i << " is not included in the " << i+1 << " column" << std::endl;
        }
      }
      //add one column for the value of the threshold T (after a sign change since it passed on the left side of the inequality)
      column[j] = Ncol;
      row[j] = -1;

      //print the vectors for debugging
      //for (int k = 0; k <= j; ++k)
      //{
      //  std::cout << row[k] << std::endl;
      //}

      //add constraint
      if (!add_constraintex(lp, Ncol, row, column, GE, 0))
        check = false;
    }
  }
  if(check)
  {
    //constraints for the OFF-SET
    for (cube cube : off_set)
    {
      j = 0;
      for (int i = 0; i < Ncol - 1; ++i) //-1 because the column for T will be created apart
      {
        if (!cube.get_mask(i)) //when the variable i does not belong to the OFF-set cube add 1 as weight factor
        {
          column[j] = i + 1; //the number of columns starts from 1
          row[j] = 1;        //the weight is 1 when present, otherwise it is 0
          ++j;
          //std::cout << "The variable " << i << " is included in the " << i+1 << " column" << std::endl;
        }
        else //when the variable i belongs to the OFF-set cube add 0 as weight factor
        {
          column[j] = i + 1; //the number of columns starts from 1
          row[j] = 0;        //the weight is 1 when present, otherwise it is 0
          ++j;
          //std::cout << "The variable " << i << " is not included in the " << i+1 << " column" << std::endl;
        }
      }
      //add one column for the value of the threshold T (after a sign change since it passed on the left side of the inequality)
      column[j] = Ncol;
      row[j] = -1;

      //print the vectors for debugging
      //for (int k = 0; k <= j; ++k)
      //{
      //  std::cout << row[k] << std::endl;
      //}

      //add constraint
      if (!add_constraintex(lp, Ncol, row, column, LE,- 1))
        check = false;
    }
  }

  //constraint all weights and threshold >= 0
  for (int i = 0u; i < Ncol; ++i)
  {
    for (int k = 0u; k < Ncol; ++k)
    {
      if (i == k)
      {
        column[i] = i + 1;
        row[i] = 1;
      }
      else
      {
        column[k] = k + 1;
        row[k] = 0;
      }
    }
    //add constraint
    if (!add_constraintex( lp, Ncol, row, column, GE,0 ))
      check = false;
  }
  set_add_rowmode(lp, FALSE); /* rowmode should be turned off again when done building the model */

  if(check)
  {
    //define the objective function to minimize
    for (int i = 0u; i < Ncol; ++i)
    {
      column[i] = i + 1;
      row[i] = 1;
    }
    set_obj_fnex(lp, Ncol , row, column);
  }

  if(check)
  {
    /* set the object direction to maximize */
    set_minim(lp);

    /* I only want to see important messages on screen while solving */
    set_verbose(lp, IMPORTANT);

    if (solve(lp) != OPTIMAL)
    {
      std::cout << "The function is unate, but it is not a TF" << std::endl;
      return false;
    }
    else
    {
      //if tt is TF: */
      std::cout << "The function is a TF" << std::endl;
      /* push the weight and threshold values into `linear_form` */
      get_variables(lp, row);
      auto new_threshold = row[Ncol - 1];
      for (auto i = 0u; i < num_vars; ++i)
      {
        if(builder[i]) //if no flip operation occurred, i.e. the function is positive unate
          linear_form.emplace_back(row[i]);
        else
        {
          linear_form.emplace_back(-row[i]); //if flip occurred, i.e. the function is negative unate
          new_threshold = new_threshold - row[i]; //update of the threshold in case of flipping according to the formula on the paper
        }
      }
      linear_form.emplace_back(new_threshold); //add the new threshold as last element

      if (plf)
      {
        *plf = linear_form;
      }
      return true;
    }
  }

  /* free allocated memory */
  if(row != nullptr)
    free(row);
  if(column != nullptr)
    free(column);

  if(lp != nullptr) {
    /* clean up such that all used memory by lpsolve is freed */
    delete_lp(lp);
  }
  return false; //just because all the lp algorithm runs only if check == true, this is to close the other branch
}

} /* namespace kitty */
