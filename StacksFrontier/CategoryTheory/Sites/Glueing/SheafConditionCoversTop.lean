module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Over

/-!
# The sheaf condition for a finer topology is local on a covering family of the final object

Let `C` be a category carrying two Grothendieck topologies, a coarse one `K` and a fine one `J`,
and let `P` be a presheaf on `C` which is a `K`-sheaf.  Let `Y : I → C` be a family of objects
covering the final object for `K`, in the sense of
`CategoryTheory.GrothendieckTopology.CoversTop`, and suppose that the restriction of `P` to each
slice site `C/Y i` is a sheaf for the localization of the *fine* topology.  Then `P` is a
`J`-sheaf.

This is the local-to-global step the comparison of quasi-coherent modules for two topologies
needs: a module which is locally, on a covering family for the coarse topology, the associated
module of a quasi-coherent module is locally a sheaf for the fine topology, and that plus the
coarse sheaf condition is all that is available.

The proof is the classical one.  Write `U` for the sieve `Sieve.ofObjects Y X` of an object `X`,
which is `K`-covering, and let `R` be a `J`-covering sieve of `X`.  For an arrow `f : Z ⟶ X` of
`U` the object `Z` admits a morphism to some `Y i`, so the slice sheaf condition at `Y i`,
transported along `CategoryTheory.Sieve.overEquiv`, makes `P` a sheaf for every `J`-covering
sieve of `Z` — in particular for `R.pullback f`.  Binding those over `U` gives a subsieve of `R`
for which `P` is a sheaf, by `CategoryTheory.Presieve.isSheafFor_bind`, and the sheaf condition
transfers from it to `R` by `CategoryTheory.Presieve.isSheafFor_subsieve_aux`, whose separation
hypothesis is supplied by `U` again.

## Main results

* `CategoryTheory.Presieve.isSheafFor_of_isSheafFor_overEquiv_symm`: the sheaf condition for a
  sieve of `b.left` is the sheaf condition on the slice site for the transported sieve at `b`.
* `CategoryTheory.Presieve.isSheaf_of_coversTop_of_isSheaf_over` and
  `CategoryTheory.Presheaf.isSheaf_of_coversTop_of_isSheaf_over`: **a `K`-sheaf whose
  restrictions to the slices at a `K`-covering family of the final object are `J`-sheaves is a
  `J`-sheaf**, for presheaves of sets and for presheaves with values in an arbitrary category.

## References

* [Stacks Project, Tag 00ZB](https://stacks.math.columbia.edu/tag/00ZB)
* [Stacks Project, Tag 0GWK](https://stacks.math.columbia.edu/tag/0GWK)
-/

@[expose] public section

open CategoryTheory Opposite

universe w v₁ u₁ v₂ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

namespace Presieve

/-- **The sheaf condition read on a slice site.**  For an object `b` of `C/W` and a sieve `S` of
the underlying object `b.left`, a presheaf of sets is a sheaf for `S` as soon as its restriction
to `C/W` is a sheaf at `b` for the sieve `CategoryTheory.Sieve.overEquiv` transports `S` to: the
arrows of the transported sieve are the arrows of `S`, read as morphisms of `C/W`. -/
theorem isSheafFor_of_isSheafFor_overEquiv_symm (P : Cᵒᵖ ⥤ Type w) {W : C} (b : Over W)
    (S : Sieve b.left)
    (h : Presieve.IsSheafFor ((Over.forget W).op ⋙ P)
      (((Sieve.overEquiv b).symm S : Sieve b) : Presieve b)) :
    Presieve.IsSheafFor P (S : Presieve b.left) := by
  intro x hx
  set x' : Presieve.FamilyOfElements ((Over.forget W).op ⋙ P)
      ((Sieve.overEquiv b).symm S).arrows :=
    fun _ g hg => x g.left ((Sieve.overEquiv_symm_iff S g).mp hg) with hx'def
  have hx' : x'.Compatible := by
    intro b₁ b₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
    exact hx g₁.left g₂.left _ _ (by
      have := (Over.forget W).congr_map hcomm
      simpa using this)
  have amalg : ∀ t : P.obj (op b.left), x.IsAmalgamation t ↔ x'.IsAmalgamation t := by
    intro t
    refine ⟨fun ht c g hg => ht g.left _, fun ht Z g hg => ?_⟩
    have hg' : ((Sieve.overEquiv b).symm S).arrows
        (Over.homMk g rfl : Over.mk (g ≫ b.hom) ⟶ b) :=
      (Sieve.overEquiv_symm_iff S (Over.homMk g rfl : Over.mk (g ≫ b.hom) ⟶ b)).mpr hg
    exact ht (Over.homMk g rfl : Over.mk (g ≫ b.hom) ⟶ b) hg'
  obtain ⟨t, ht, huniq⟩ := h x' hx'
  exact ⟨t, (amalg t).mpr ht, fun t' ht' => huniq t' ((amalg t').mp ht')⟩

/-- **A `K`-sheaf of sets whose restrictions to the slices at a `K`-covering family of the final
object are `J`-sheaves is a `J`-sheaf.** -/
theorem isSheaf_of_coversTop_of_isSheaf_over (K J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ Type w)
    (hPK : Presieve.IsSheaf K P) {I : Type*} {Y : I → C} (hY : K.CoversTop Y)
    (hslice : ∀ i, Presieve.IsSheaf (J.over (Y i)) ((Over.forget (Y i)).op ⋙ P)) :
    Presieve.IsSheaf J P := by
  intro X R hR
  have hUK : Sieve.ofObjects Y X ∈ K X := hY X
  have key : ∀ ⦃Z : C⦄ ⦃f : Z ⟶ X⦄, (Sieve.ofObjects Y X) f → ∀ T : Sieve Z, T ∈ J Z →
      Presieve.IsSheafFor P (T : Presieve Z) := by
    rintro Z f ⟨i, ⟨g⟩⟩ T hT
    exact isSheafFor_of_isSheafFor_overEquiv_symm P (Over.mk g) T
      (hslice i _ (J.overEquiv_symm_mem_over (Over.mk g) T hT))
  have hbindle : (Sieve.bind (Sieve.ofObjects Y X : Presieve X)
      (fun _ f _ => R.pullback f) : Presieve X) ≤ (R : Presieve X) := by
    rintro Z h ⟨Z', g, f, hf, hg, rfl⟩
    exact hg
  have hB : ∀ ⦃Z : C⦄ ⦃f : Z ⟶ X⦄ (_ : (Sieve.ofObjects Y X) f),
      Presieve.IsSheafFor P (R.pullback f : Presieve Z) :=
    fun _ _ hf => key hf _ (J.pullback_stable _ hR)
  have hB' : ∀ ⦃Z : C⦄ ⦃f : Z ⟶ X⦄ (_ : (Sieve.ofObjects Y X) f) ⦃Z' : C⦄ (g : Z' ⟶ Z),
      Presieve.IsSeparatedFor P (((R.pullback f).pullback g) : Presieve Z') :=
    fun _ _ hf _ g => (key ((Sieve.ofObjects Y X).downward_closed hf g) _
      (J.pullback_stable g (J.pullback_stable _ hR))).isSeparatedFor
  refine Presieve.isSheafFor_subsieve_aux P hbindle
    (Presieve.isSheafFor_bind P _ (fun _ f _ => R.pullback f) (hPK _ hUK) hB hB') ?_
  intro Z f hf
  have hle : ((Sieve.ofObjects Y X).pullback f : Presieve Z) ≤
      ((Sieve.bind (Sieve.ofObjects Y X : Presieve X)
        (fun _ f _ => R.pullback f)).pullback f : Presieve Z) := by
    intro Z' g hg
    have hR' : (R.pullback (g ≫ f)).arrows (𝟙 Z') := by
      simpa using R.downward_closed hf g
    have := Presieve.bind_comp (S := (Sieve.ofObjects Y X : Presieve X))
      (R := fun _ f _ => (R.pullback f : Presieve _)) (g ≫ f) hg hR'
    simpa using this
  have hsep : Presieve.IsSeparatedFor P
      ((Sieve.ofObjects Y X).pullback f : Presieve Z) :=
    (hPK _ (K.pullback_stable f hUK)).isSeparatedFor
  intro x t₁ t₂ h₁ h₂
  exact hsep _ _ _ (Presieve.isAmalgamation_restrict hle x t₁ h₁)
    (Presieve.isAmalgamation_restrict hle x t₂ h₂)

end Presieve

/-- **A `K`-sheaf whose restrictions to the slices at a `K`-covering family of the final object
are `J`-sheaves is a `J`-sheaf**, for presheaves with values in an arbitrary category: the sheaf
condition is the sheaf condition of each presheaf of sets obtained by mapping into an object. -/
theorem Presheaf.isSheaf_of_coversTop_of_isSheaf_over (K J : GrothendieckTopology C)
    {A : Type u₂} [Category.{v₂} A] (P : Cᵒᵖ ⥤ A) (hPK : Presheaf.IsSheaf K P)
    {I : Type*} {Y : I → C} (hY : K.CoversTop Y)
    (hslice : ∀ i, Presheaf.IsSheaf (J.over (Y i)) ((Over.forget (Y i)).op ⋙ P)) :
    Presheaf.IsSheaf J P :=
  fun E => Presieve.isSheaf_of_coversTop_of_isSheaf_over K J _ (hPK E) hY fun i => hslice i E

/-- **The sheaf condition read along an equivalence of sites.**  If `e : C ≌ D` is continuous in
both directions for a topology `J` on `C` and a topology `K` on `D`, then a presheaf on `D` whose
composite with `e.functor` is a `J`-sheaf is a `K`-sheaf: compose with `e.inverse`, which is
continuous, and transport along the counit of `e`. -/
theorem Presheaf.isSheaf_of_isSheaf_comp_equivalence {D : Type u₂} [Category.{v₂} D] (e : C ≌ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [e.inverse.IsContinuous K J] {A : Type*} [Category A] (Q : Dᵒᵖ ⥤ A)
    (h : Presheaf.IsSheaf J (e.functor.op ⋙ Q)) :
    Presheaf.IsSheaf K Q :=
  (Presheaf.isSheaf_of_iso_iff (Functor.isoWhiskerRight (NatIso.op e.counitIso) Q)).2
    (Functor.op_comp_isSheaf_of_isSheaf e.inverse K J _ h)

end CategoryTheory

end
