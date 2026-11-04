module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.QuasiIso
public import StacksFrontier.RingTheory.Cech.PresheafComplex

/-!
# Independence of the generating family, for the presheaf of Čech complexes

Let `R` be a presheaf of commutative rings and let `f₁, …, f_r` be a subfamily of `g₁, …, g_s`,
both families of sections of `R` over every object and compatible with restriction. If over every
object the two families span the same ideal of sections, then the restriction map

`K(R(-), (g₁, …, g_s)) ⟶ K(R(-), (f₁, …, f_r))`

of `PresheafComplex.lean` is a **quasi-isomorphism** of complexes of presheaves of modules.

Together with `Stacks.IdealCechComplex.restrictObjHom_comp_canonicalHom`, which exhibits the
comparison of two arbitrary families as the zig-zag through their concatenation, this is the
independence of the chosen finite generating family that [Stacks, Tag 099E] needs in order to
sheafify: a quasi-isomorphism of presheaf complexes over `R`, not merely an isomorphism in the
derived category of each ring of sections, which is all that
`Stacks.IdealCechComplex.canonicalIso` supplies and which cannot be sheafified.

## Main results

* `Stacks.CechPresheaf.quasiIso_cechRestrict`: **restriction to a subfamily spanning the same
  ideal is a quasi-isomorphism** of the `ℕ`-indexed complexes of modules. This is
  `Stacks.IdealCechComplex.isIso_restrictObjHom_of_span_eq` read through
  `CategoryTheory.HomologicalComplex.quasiIso_extendMap_iff`.
* `Stacks.CechPresheaf.quasiIso_cechPresheafRestrictNat`: **the restriction map of the presheaf
  complexes is a quasi-isomorphism** when the two families span the same ideal of sections over
  every object.

## References

* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.CechPresheaf

section Ring

variable {A : Type u} [CommRing A] {r s : ℕ} (f : Fin r → A) (g : Fin s → A)
  (e : Fin r ↪o Fin s) (he : ∀ i, g (e i) = f i) (M : ModuleCat.{u} A)

/-- **Restriction to a subfamily spanning the same ideal is a quasi-isomorphism** of the
`ℕ`-indexed Čech complexes. The `ℤ`-indexed statement in the derived category is
`Stacks.IdealCechComplex.isIso_restrictObjHom_of_span_eq`; a map of `ℕ`-indexed complexes is a
quasi-isomorphism exactly when its extension along `ComplexShape.embeddingUpNat` is. -/
theorem quasiIso_cechRestrict
    (hgf : Ideal.span (Set.range g) = Ideal.span (Set.range f)) :
    QuasiIso (Cech.cechRestrict f M g e he) := by
  rw [← HomologicalComplex.quasiIso_extendMap_iff _ ComplexShape.embeddingUpNat,
    ← DerivedCategory.isIso_Q_map_iff_quasiIso]
  exact Stacks.IdealCechComplex.isIso_restrictObjHom_of_span_eq f g e he M hgf

end Ring

section Presheaf

variable {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ CommRingCat.{u}) {r s : ℕ}
  (f : ∀ V : Cᵒᵖ, Fin r → R.obj V)
  (hf : ∀ {V W : Cᵒᵖ} (a : V ⟶ W) (i : Fin r), (R.map a).hom (f V i) = f W i)
  (g : ∀ V : Cᵒᵖ, Fin s → R.obj V)
  (hg : ∀ {V W : Cᵒᵖ} (a : V ⟶ W) (j : Fin s), (R.map a).hom (g V j) = g W j)
  (e : Fin r ↪o Fin s) (he : ∀ (V : Cᵒᵖ) (i : Fin r), g V (e i) = f V i)

/-- **The restriction map of the presheaf of Čech complexes onto a subfamily is a
quasi-isomorphism** as soon as the two families span the same ideal of sections over every
object. -/
theorem quasiIso_cechPresheafRestrictNat
    (hspan : ∀ V : Cᵒᵖ, Ideal.span (Set.range (g V)) = Ideal.span (Set.range (f V))) :
    QuasiIso (cechPresheafRestrictNat R f hf g hg e he) := by
  refine PresheafOfModules.quasiIso_of_forall_quasiIso_evaluation _ fun V => ?_
  rw [evaluation_map_cechPresheafRestrictNat]
  have : QuasiIso (Cech.cechRestrict (f V) (ModuleCat.of (R.obj V) (R.obj V)) (g V) e (he V)) :=
    quasiIso_cechRestrict (f V) (g V) e (he V) (ModuleCat.of (R.obj V) (R.obj V)) (hspan V)
  infer_instance

end Presheaf

end Stacks.CechPresheaf

end
