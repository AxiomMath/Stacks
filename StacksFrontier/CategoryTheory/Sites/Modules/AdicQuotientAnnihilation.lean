module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import StacksFrontier.CategoryTheory.Sites.Modules.AdicQuotientModuleTower
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealTensorVanishing

/-!
# The powers of a sheaf of ideals annihilate the corresponding quotient of the structure sheaf

Let `(C, O)` be a ringed site and `I ⊆ O` a sheaf of ideals. The sections of `Iⁿ` kill the
sections of `O/Iⁿ`, and consequently multiplication by a compatible family of local sections of
`Iⁿ` is the zero endomorphism of `O/Iⁿ`.

## Main results

* `Stacks.Sites.smul_adicQuotientModule_eq_zero`: a section of `Iⁿ` kills every section of
  `O/Iⁿ`.
* `Stacks.Sites.globalSectionToEnd_app_adicQuotientModule_eq_zero`: multiplication by a
  compatible family of local sections of `Iⁿ` vanishes on `O/Iⁿ`.

## Implementation notes

`O/Iⁿ` is `Stacks.Sites.adicQuotientModule`, the cokernel in sheaves of `O`-modules of the
inclusion of `Iⁿ` into the free rank-one sheaf of modules, so its sections over an object are
*not* the quotient of the sections there: the cokernel is a sheafification. The annihilation is
therefore proved the way `Stacks.Sites.smul_adicGradedPiece_eq_zero` is: the projection
`O ⟶ O/Iⁿ` is an epimorphism of sheaves of modules, hence locally surjective, so a section of
`O/Iⁿ` is, after restriction along the arrows of some covering sieve, the image of a section `s`
of `O`; there the product with a section `a` of `Iⁿ` is the image of `a · s`, which lies in `Iⁿ`
because `Iⁿ` is a sheaf of ideals, and so dies under the projection. A sheaf is separated, so
the product vanishes outright.

The second statement is the first read through
`Stacks.SheafOfModules.globalSectionToEnd`, the endomorphism of the *identity* functor of
`Mod(O)` given by multiplication by a compatible family of local sections. That form is what the
derived-completeness predicate of [Stacks, Tag 0999] consumes, through the linear structure on
`Mod(O)` over the centre of its own category.

## References

* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe w v u

namespace Stacks.Sites

open AlgebraicGeometry.RingedSite

variable {X : RingedSite.{u, v, w}}

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The image in `O/Iⁿ` of a section of `O` is killed by every section of `Iⁿ`.** The product
of a section of `Iⁿ` with a section of `O` is again a section of `Iⁿ`, hence dies under the
projection onto the cokernel of the inclusion of `Iⁿ`. -/
theorem smul_adicQuotientModuleπ_app_eq_zero (I : IdealSubsheaf.{v, u, w} X.O) (n : ℕ)
    (V : X.Cᵒᵖ) (a : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj V)
    (ha : a ∈ (idealPow I n).obj V)
    (s : (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))).val.obj V) :
    a • (adicQuotientModuleπ I n).val.app V s = 0 := by
  have key : ∀ b c : ToType (X.O.obj.obj V),
      b ∈ ((idealPow I n).obj V : Ideal (ToType (X.O.obj.obj V))) →
        b * c ∈ ((idealPow I n).obj V : Ideal (ToType (X.O.obj.obj V))) := by
    intro b c hb
    rw [mul_comm]
    exact Ideal.mul_mem_left _ _ hb
  have hmem : a • s ∈ (idealPow I n).obj V := key a s ha
  rw [← map_smul]
  exact Stacks.SheafOfModules.val_app_apply_eq_zero _ _
    (ι_comp_adicQuotientModuleπ I n) V ⟨a • s, hmem⟩

/-- **The sections of `Iⁿ` kill the sections of `O/Iⁿ`.** A section of `O/Iⁿ` is, after
restriction along the arrows of some covering sieve, the image of a section of `O`, because the
projection onto the quotient is an epimorphism of sheaves of modules and hence locally
surjective; there the product with a section of `Iⁿ` vanishes. A sheaf is separated, so the
product vanishes outright. -/
theorem smul_adicQuotientModule_eq_zero (I : IdealSubsheaf.{v, u, w} X.O) (n : ℕ) (U : X.Cᵒᵖ)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
    (ha : a ∈ (idealPow I n).obj U)
    (g : (adicQuotientModule I n).val.obj U) : a • g = 0 := by
  obtain ⟨S, hS, hlift⟩ :=
    Stacks.SheafOfModules.EpiMono.exists_covering_of_epi (adicQuotientModuleπ I n) g
  refine Stacks.SheafOfModules.eq_zero_of_locally_eq_zero _ hS fun {V} f hf => ?_
  obtain ⟨t, ht⟩ := hlift f hf
  rw [PresheafOfModules.map_smul, ← show (adicQuotientModuleπ I n).val.app (op V) t =
    (adicQuotientModule I n).val.map f.op g from ht]
  exact smul_adicQuotientModuleπ_app_eq_zero I n (op V) _ ((idealPow I n).map_mem f.op ha) t

/-- **Multiplication by a compatible family of local sections of `Iⁿ` vanishes on `O/Iⁿ`.** This
is `Stacks.Sites.smul_adicQuotientModule_eq_zero` read as the vanishing of the value at `O/Iⁿ`
of the endomorphism of the identity functor of `Mod(O)` given by that family. -/
theorem globalSectionToEnd_app_adicQuotientModule_eq_zero (I : IdealSubsheaf.{v, u, w} X.O)
    (n : ℕ) (a : (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj ⋙ forget RingCat.{w}).sections)
    (ha : ∀ U : X.Cᵒᵖ, a.val U ∈ (idealPow I n).obj U) :
    (Stacks.SheafOfModules.globalSectionToEnd ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      a).asHom.app
      (adicQuotientModule I n) = 0 := by
  refine _root_.SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun U => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun g => ?_)
  exact smul_adicQuotientModule_eq_zero I n U (a.val U) (ha U) g

end Stacks.Sites

end
