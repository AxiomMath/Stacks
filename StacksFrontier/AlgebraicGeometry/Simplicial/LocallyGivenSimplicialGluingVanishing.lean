module

public import StacksFrontier.AlgebraicGeometry.Simplicial.LocallyGivenDerived
public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableSummandRestriction
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Basic

/-!
# Vanishing of shifted maps on the components of a simplicial semi-representable site

Let `(C, O_C)` be a ringed site, `K` a simplicial semi-representable object of `C` with
`K_n = {U_{n,i}}_{i ∈ I_n}`, and `O_n` the restriction to the component `C/K_n` of the sheaf of
rings `O = a⁻¹O_C` of Remark 0D9W. The summand restrictions identify `D(O_n)` with
`∏_{i ∈ I_n} D(O_{U_{n,i}})`. They commute with shifts, and maps in a product of categories are
families of maps. Hence a map `A[t] ⟶ B` of `D(O_n)` vanishes as soon as each of its summand
restrictions does.

In the proof of Stacks 0DCA this is the step "the vanishing of negative exts assumed in the
lemma implies that `Hom(E_n[t], E_n) = 0` for `n ≥ 0` and `t > 0`": if the restrictions of `A`
and `B` to every summand `C/u(U_{n,i})` are isomorphic to the locally given object
`E_{U_{n,i}}`, whose negative self-exts vanish, then `Hom(A[t], B) = 0` for every `t > 0`. This
gives at once the vanishing hypotheses of Stacks 0D9T (`Hom(E_n[t], E_n) = 0`) and those of
Stacks 0D9S and Stacks 0D9R (`Hom(K_i[i - 1], K'_i) = 0` for `i > 1`, `Hom(K_i[i], K'_i) = 0`
for `i > 0`, `Hom(K_i[i + 1], K'_i) = 0` for `i ≥ 0`), for any two objects restricting to the
`E_{U_{n,i}}`.

## Main results

* `CategoryTheory.Functor.shift_hom_eq_zero_of_pi'`: along a faithful family of functors commuting
  with shifts, a shifted map vanishes when all its images do.
* `CategoryTheory.SimplicialSemiRepresentable.derivedSummandRestriction_shift_hom_eq_zero`: a
  shifted map of `D(O_n)` between objects whose summand restrictions are isomorphic to objects
  with vanishing shifted self-maps is zero.
* `AlgebraicGeometry.RingedSite.LocallyGiven.shift_hom_eq_zero_of_summandIso`: for `K = u(L)`, if
  the negative self-exts of the `E_U` vanish, then `Hom(A[t], B) = 0` in `D(O_n)` for `t > 0` and
  any `A`, `B` restricting to the `E_{U_{n,i}}`.

## Implementation notes

The simplicial object `K = u(L)` is written `L ⋙ mapFormalCoproduct G.u`, which is
`AlgebraicGeometry.RingedSite.LocallyGiven.image` by definition. The structure sheaf `O_n` takes
sections in the universe `u` of the site, so the locally given objects are taken with the
additional module universe `0`, for which `LocalDerivedCategory` is the derived category of
modules in the universe `u`; the summandwise statement
`CategoryTheory.SimplicialSemiRepresentable.derivedSummandRestriction_shift_hom_eq_zero` has no
such restriction.

## References

* [Stacks Project, Tag 0DCA](https://stacks.math.columbia.edu/tag/0DCA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor

universe w v₁ u₁ v₂ u₂

variable {M : Type*} [AddMonoid M] {𝒟 : Type u₁} [Category.{v₁} 𝒟] [HasZeroMorphisms 𝒟]
  [HasShift 𝒟 M] {ι : Type w} {𝒟' : ι → Type u₂} [∀ i, Category.{v₂} (𝒟' i)]
  [∀ i, HasZeroMorphisms (𝒟' i)] [∀ i, HasShift (𝒟' i) M] (F : ∀ i, 𝒟 ⥤ 𝒟' i)
  [∀ i, (F i).CommShift M] [∀ i, (F i).PreservesZeroMorphisms] [(Functor.pi' F).Faithful]

/-- **Shifted maps vanish componentwise.** If the functors `F i` commute with shifts and jointly
form a faithful functor to `∏ i, 𝒟' i`, a map `A⟦t⟧ ⟶ B` vanishes as soon as every map
`(F i A)⟦t⟧ ⟶ F i B` does. -/
theorem shift_hom_eq_zero_of_pi' {A B : 𝒟} (t : M)
    (h : ∀ i, ∀ g : (shiftFunctor (𝒟' i) t).obj ((F i).obj A) ⟶ (F i).obj B, g = 0)
    (g : (shiftFunctor 𝒟 t).obj A ⟶ B) : g = 0 := by
  refine (Functor.pi' F).map_injective (funext fun i => ?_)
  change (F i).map g = (F i).map 0
  rw [Functor.map_zero]
  have hi := h i (((F i).commShiftIso t).inv.app A ≫ (F i).map g)
  rw [← cancel_epi (((F i).commShiftIso t).inv.app A), hi, comp_zero]

end CategoryTheory.Functor

namespace CategoryTheory.SimplicialSemiRepresentable

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : AlgebraicGeometry.RingedSite.{u, u, u}) [X.J.toCoverage.HasPullbacks]
  (K : SimplicialObject (FormalCoproduct.{u} X.C))

/-- **Shifted maps in `D(O_n)` vanish summandwise.** Let `A`, `B` be objects of `D(O_n)` whose
restrictions to the summands `C/U_{n,i}` are isomorphic to objects `T i` of `D(O_{U_{n,i}})`
with vanishing shifted self-maps `T i⟦t⟧ ⟶ T i`. Then every map `A⟦t⟧ ⟶ B` is zero. -/
theorem derivedSummandRestriction_shift_hom_eq_zero (n : SimplexCategory)
    (T : ∀ i : (K.obj (op n)).I,
      DerivedCategory (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over ((K.obj (op n)).obj i))))
    (A B : DerivedCategory (SheafOfModules.{u} (componentRing X K n)))
    (a : ∀ i, (summandRestriction X K n i).mapDerivedCategory.obj A ≅ T i)
    (b : ∀ i, (summandRestriction X K n i).mapDerivedCategory.obj B ≅ T i) (t : ℤ)
    (hT : ∀ i, ∀ g : (shiftFunctor _ t).obj (T i) ⟶ T i, g = 0)
    (g : (shiftFunctor _ t).obj A ⟶ B) : g = 0 := by
  refine Functor.shift_hom_eq_zero_of_pi' (fun i => (summandRestriction X K n i).mapDerivedCategory)
    t (fun i g => ?_) g
  have h := hT i ((shiftFunctor _ t).map (a i).inv ≫ g ≫ (b i).hom)
  have e : g = (shiftFunctor _ t).map (a i).hom ≫
      ((shiftFunctor _ t).map (a i).inv ≫ g ≫ (b i).hom) ≫ (b i).inv := by
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, ← Functor.map_comp_assoc,
      Iso.hom_inv_id, Functor.map_id, Category.id_comp]
  rw [e, h, zero_comp, comp_zero]

end CategoryTheory.SimplicialSemiRepresentable

namespace AlgebraicGeometry.RingedSite

universe u uB vB

attribute [local instance] LocallyGiven.category HasDerivedCategory.standard

open CategoryTheory.SimplicialSemiRepresentable Stacks.CategoryTheory.Hypercovering

variable {X : RingedSite.{u, u, u}} [X.J.toCoverage.HasPullbacks]
  (G : LocallyGiven.{0, u, u, u, uB, vB} X) (L : SimplicialObject (FormalCoproduct.{u} G.B))

/-- **Negative self-exts of the `E_U` give vanishing shifted maps in `D(O_n)`.** Let `K = u(L)`.
If the negative self-exts of every locally given object `E_U` vanish, then for `t > 0` every
map `A⟦t⟧ ⟶ B` of `D(O_n)` is zero, whenever the restrictions of `A` and `B` to every summand
`C/u(U_{n,i})` of the degree-`n` component are isomorphic to `E_{U_{n,i}}`. -/
theorem LocallyGiven.shift_hom_eq_zero_of_summandIso
    (hneg : ∀ (U : G.B) (t : ℤ), 0 < t →
      ∀ g : (shiftFunctor (LocalDerivedCategory.{0} X (G.u.obj U)) t).obj (G.obj U) ⟶ G.obj U,
        g = 0)
    (n : SimplexCategory)
    (A B : DerivedCategory (SheafOfModules.{u} (componentRing X (L ⋙ mapFormalCoproduct G.u) n)))
    (a : ∀ i : ((L ⋙ mapFormalCoproduct G.u).obj (op n)).I,
      (summandRestriction X (L ⋙ mapFormalCoproduct G.u) n i).mapDerivedCategory.obj A ≅
        G.obj ((L.obj (op n)).obj i))
    (b : ∀ i : ((L ⋙ mapFormalCoproduct G.u).obj (op n)).I,
      (summandRestriction X (L ⋙ mapFormalCoproduct G.u) n i).mapDerivedCategory.obj B ≅
        G.obj ((L.obj (op n)).obj i))
    (t : ℤ) (ht : 0 < t) (g : (shiftFunctor _ t).obj A ⟶ B) : g = 0 :=
  derivedSummandRestriction_shift_hom_eq_zero X (L ⋙ mapFormalCoproduct G.u) n
    (fun i => G.obj ((L.obj (op n)).obj i)) A B a b t
    (fun i => hneg ((L.obj (op n)).obj i) t ht) g

end AlgebraicGeometry.RingedSite
