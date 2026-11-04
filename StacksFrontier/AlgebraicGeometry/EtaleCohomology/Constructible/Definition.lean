module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructible abelian and module sheaves on a small étale site, without coefficient hypotheses

Parts (2) and (3) of Tag 03RW, constructible sheaves of abelian groups and of `Λ`-modules on
`X_étale`, are stated in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible` for a free
coefficient universe. There each predicate takes two typeclass arguments: that the direct image
along small étale base change is a right adjoint, so that the restriction `F|_{U_i}` to a stratum
exists, and that the localizations of a small étale site admit weak sheafification, so that local
constancy can be stated. Both are theorems, not hypotheses of the source.

This file states the two parts at the coefficient universe `max (u + 1) w`, which dominates the
universe `u + 1` indexing the coverings of the small étale site of Tag 021B. At that universe both
arguments are found by instance search
(`Stacks.ConstantSheaf.hasWeakSheafify_addCommGrp_of_univLE` and
`Stacks.ConstantSheaf.hasSheafify_moduleCat_of_univLE`), so the definitions below take no
typeclass argument beyond the source's hypothesis that `Λ` be a Noetherian ring. Part (1),
constructible sheaves of sets, is `AlgebraicGeometry.IsConstructibleSetSheaf`, which already
takes no such argument.

## Main definitions

* `AlgebraicGeometry.IsConstructibleAbelianEtaleSheaf`: part (2), a constructible sheaf of
  abelian groups on `X_étale`.
* `AlgebraicGeometry.IsConstructibleModuleEtaleSheaf`: part (3), a constructible sheaf of
  `Λ`-modules on `X_étale`, for `Λ` a Noetherian ring.

## Main results

* `AlgebraicGeometry.isConstructibleAbelianEtaleSheaf_iff` and
  `AlgebraicGeometry.isConstructibleModuleEtaleSheaf_iff`: they agree with
  `AlgebraicGeometry.IsConstructibleAbelianSheaf` and
  `AlgebraicGeometry.IsConstructibleModuleSheaf` at this coefficient universe, with the typeclass
  arguments of the latter discharged by instance search; for part (3) this also identifies "of
  finite type and locally constant" with local constancy with finitely generated values. So every
  result proved about those applies here.

## Implementation notes

The clauses are those of the source. For every affine open `U ⊆ X` there is a
`AlgebraicGeometry.ConstructibleStratification` of `U`: finitely many immersions `U_i → X` with
pairwise disjoint images covering `U`, each image a constructible subset of `U`. The restriction
`F|_{U_i}` is the inverse image along small étale base change by `U_i → X`, which is the inverse
image along the immersion. The source notes that the scheme structure of a stratum does not matter
by topological invariance of the étale site (Theorem 04DZ); the definition quantifies over all
immersions, which includes the reduced ones.

For abelian groups `F|_{U_i}` is asked to be finite locally constant
(`Stacks.ConstantSheaf.IsFiniteLocallyConstant`, Tag 093Q (3)): on a covering of every object it
is the constant sheaf on a finite abelian group. For `Λ`-modules it is asked, as in the source, to
be of finite type (`Stacks.ConstantSheaf.IsFiniteTypeModuleSheaf`, Tag 03DL (5): locally generated
by finitely many sections) and locally constant (`Stacks.ConstantSheaf.IsLocallyConstant`,
Tag 093Q (2)). The base predicate instead asks for local constancy with finitely generated
values; the two agree by `Stacks.ConstantSheaf.isFiniteTypeModuleSheaf_and_isLocallyConstant_iff`,
which is what `AlgebraicGeometry.isConstructibleModuleEtaleSheaf_iff` uses.

## References

* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- **Stacks 03RW (2).** A sheaf of abelian groups `F` on the small étale site of `X` is
constructible if for every affine open `U ⊆ X` there is a finite decomposition `U = ∐ᵢ Uᵢ` into
constructible locally closed subschemes such that `F|_{Uᵢ}` is finite locally constant for
all `i`. -/
@[stacks 03RW "part (2)", sga "4 IX 2.3" "special case", sga "4½ Arcata 4.3.2"]
public abbrev IsConstructibleAbelianEtaleSheaf
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) w}) : Prop :=
  ∀ U : X.obj.affineOpens, ∃ s : ConstructibleStratification B X U.1,
    ∀ i, Stacks.ConstantSheaf.IsFiniteLocallyConstant
      (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
      (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback AddCommGrpCat.{max (u + 1) w}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj F)

/-- **Stacks 03RW (3).** Let `Λ` be a Noetherian ring. A sheaf of `Λ`-modules `F` on the small
étale site of `X` is constructible if for every affine open `U ⊆ X` there is a finite
decomposition `U = ∐ᵢ Uᵢ` into constructible locally closed subschemes such that `F|_{Uᵢ}` is of
finite type and locally constant for all `i`. -/
@[stacks 03RW "part (3)"]
public abbrev IsConstructibleModuleEtaleSheaf (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)) : Prop :=
  ∀ U : X.obj.affineOpens, ∃ s : ConstructibleStratification B X U.1,
    ∀ i, Stacks.ConstantSheaf.IsFiniteTypeModuleSheaf
        (SmallEtale.topology B (s.piece i).obj (s.piece i).property) Λ
        (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj F) ∧
      Stacks.ConstantSheaf.IsLocallyConstant
        (SmallEtale.topology B (s.piece i).obj (s.piece i).property)
        (((smallEtaleBaseChange B (s.inclusion i)).sheafPullback (ModuleCat.{max (u + 1) w} Λ)
          (SmallEtale.topology B X.obj X.property)
          (SmallEtale.topology B (s.piece i).obj (s.piece i).property)).obj F)

/-- Part (2) of Tag 03RW agrees with `AlgebraicGeometry.IsConstructibleAbelianSheaf` at the
coefficient universe `max (u + 1) w`, whose typeclass arguments are found by instance search. -/
public theorem isConstructibleAbelianEtaleSheaf_iff
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) w}) :
    IsConstructibleAbelianEtaleSheaf B X F ↔ IsConstructibleAbelianSheaf B X F :=
  Iff.rfl

/-- Part (3) of Tag 03RW agrees with `AlgebraicGeometry.IsConstructibleModuleSheaf` at the
coefficient universe `max (u + 1) w`, whose typeclass arguments are found by instance search: on
each stratum, being of finite type and locally constant is being locally the constant sheaf on a
finitely generated module, by
`Stacks.ConstantSheaf.isFiniteTypeModuleSheaf_and_isLocallyConstant_iff`. -/
public theorem isConstructibleModuleEtaleSheaf_iff (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)) :
    IsConstructibleModuleEtaleSheaf B X Λ F ↔ IsConstructibleModuleSheaf B X Λ F :=
  forall_congr' fun _ => exists_congr fun _ => forall_congr' fun _ =>
    Stacks.ConstantSheaf.isFiniteTypeModuleSheaf_and_isLocallyConstant_iff _

end AlgebraicGeometry

end
