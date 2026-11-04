module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic.ExtAndYonedaExtensions
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic.YonedaClassMap
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic.ExtOneAndVanishing
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic.SplittingAndResolutions

/-!
# Ext groups

The basic facts about the extension groups of an abelian category, in four parts:

* `ExtAndYonedaExtensions`: the `Ext` groups, Yoneda extensions and their equivalence;
* `YonedaClassMap`: cutting and splicing Yoneda extensions, and the class map from Yoneda
  extensions to `Ext`;
* `ExtOneAndVanishing`: `Ext^1` and extensions, vanishing of `Ext` and projective dimension,
  vanishing of a Yoneda product of two extension classes, and `Ext` between objects of the
  derived category with disjoint homology ranges;
* `SplittingAndResolutions`: splitting a bounded complex into its cohomologies, and `Ext`
  computed by injective and projective resolutions.
-/
