module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluatingSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexOfAStrictlyPerfectComplex

/-!
# Evaluating the degree projection of an internal Hom complex

For complexes `E`, `F` of sheaves of modules on a ringed site, the degree-`n` term of the internal
Hom complex `SheafHom^•(E, F)` is a product over `q` of the internal Hom sheaves
`SheafHom(E^{-q}, F^{n-q})`, and `AlgebraicGeometry.RingedSite.homDegreeProjection` is the
projection onto one factor. When `F` is concentrated in degree zero all factors but one vanish and
the projection becomes an isomorphism.

This file says what those two maps **do to a section**: the projection reads off a component of the
corresponding cochain, which is exactly
`AlgebraicGeometry.RingedSite.applyHomSectionOver`, so a computation that knows the components of a
cochain knows the value of the projected section on any section of the source.

## Main results

* `AlgebraicGeometry.RingedSite.internalHomSheaf_eqToHom_source_app` and
  `AlgebraicGeometry.RingedSite.internalHomSheaf_eqToHom_target_app`: **a transport of either
  argument of an internal Hom sheaf acts on a section by transporting the argument**, respectively
  the value.
* `AlgebraicGeometry.RingedSite.homDegreeProjection_app_eq_applyHomSectionOver`: **the projection
  evaluated on a section of the source is the corresponding component of the cochain.**

## Implementation notes

**The transports are discharged by generalising the equality, not by pushing `eqToHom` around.**
Each of the two transport lemmas is stated with the two sheaves of modules and the equality between
them as *variables*; `subst` then replaces the equality by `rfl`, the `eqToHom` by an identity, and
the statement by a reflexivity. Applied at a concrete equality — the double negation
`E^{-(-n)} = E^n` of a reindexed complex, or the degree `n - n = 0` of a complex concentrated in
degree zero — this turns what would otherwise be `eqToHom` gymnastics into a rewrite. Nothing here
needs the transports to commute with anything; they are simply named so that a consumer can move
them out of the way.

**The equality of internal Hom sheaves is a separate variable from the equality of the arguments,
and this is what makes the lemmas usable.** Writing the transported object as
`eqToHom (congrArg (fun Z => internalHomSheaf Y Z N) hM)` would force `rw` to match the argument
`M` both inside that `congrArg` and in the type of the section being transported — and at the one
place this is needed those two are *definitionally* equal without being syntactically equal, the
degree `-n` term of a reindexed complex against the degree `n` term of the original. Taking the
equality of internal Hom sheaves as an unconstrained variable lets it be matched by unification and
leaves the equality of arguments as a side goal, which is where it can be discharged by hand.

**The projection is characterised, not unfolded.**
`AlgebraicGeometry.RingedSite.homDegreeProjection` is `public` but not `@[expose]`, so the only
handle on it is `homDegreeProjection_val_app_apply`; the bridge below is that characterisation
read through the abbreviation `applyHomSectionOver`, which names the same component of the same
cochain.

## References

* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex

universe u

namespace AlgebraicGeometry.RingedSite

variable (Y : RingedSite.{u, u, u}) [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **A transport of the source of an internal Hom sheaf acts on a section by transporting the
argument.** Proved by substituting the equality, after which both transports are identities. -/
theorem internalHomSheaf_eqToHom_source_app
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    {M M' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (hM : M = M')
    (h : internalHomSheaf Y M N = internalHomSheaf Y M' N) (U : Y.C)
    (s : (internalHomSheaf Y M N).val.obj (op U)) (W : (CategoryTheory.Over U)ᵒᵖ)
    (y : (M'.over U).val.obj W) :
    ((eqToHom h).val.app (op U) s).app W y =
      s.app W (eqToHom (congrArg
        (fun Z : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) =>
          (Z.over U).val.obj W) hM.symm) y) := by
  subst hM
  rfl

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **A transport of the target of an internal Hom sheaf acts on a section by transporting the
value.** Proved by substituting the equality. -/
theorem internalHomSheaf_eqToHom_target_app
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    {N N' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (hN : N = N')
    (h : internalHomSheaf Y M N = internalHomSheaf Y M N') (U : Y.C)
    (s : (internalHomSheaf Y M N).val.obj (op U)) (W : (CategoryTheory.Over U)ᵒᵖ)
    (y : (M.over U).val.obj W) :
    ((eqToHom h).val.app (op U) s).app W y =
      eqToHom (congrArg
        (fun Z : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) =>
          (Z.over U).val.obj W) hN) (s.app W y) := by
  subst hN
  rfl

omit [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The degree projection evaluated on a section of the source is the corresponding component of
the cochain.** The section that `homDegreeProjection` produces out of a degree-`n` section of the
internal Hom complex is, evaluated over an arrow `i : V ⟶ U` on a section of `E^{-q}`, the value of
the `(-q, n - q)` component of the corresponding cochain. -/
theorem homDegreeProjection_app_eq_applyHomSectionOver
    (E F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (n q : ℤ) (U V : Y.C) (i : V ⟶ U)
    (s : ((sheafHomComplex Y E F).obj.X n).val.obj (op U))
    (y : ((E.X (-q)).over U).val.obj (op (Over.mk i))) :
    ((homDegreeProjection Y E F n q).val.app (op U) s).app (op (Over.mk i)) y =
      applyHomSectionOver Y (sheafHomComplex Y E F) U V i n (-q) (n - q) (by omega) s y := by
  rw [homDegreeProjection_val_app_apply]
  rfl

end AlgebraicGeometry.RingedSite

end
