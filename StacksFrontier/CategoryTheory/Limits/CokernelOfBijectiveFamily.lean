module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Recognising a cokernel through a natural family of bijections

Let `F₁ : 𝒜 ⥤ ℬ₁` and `F₂ : 𝒜 ⥤ ℬ₂` be two functors and let `a : Q ⟶ P`, `b : P ⟶ N` be a cofork
in `𝒜`.  Suppose a natural family of maps

  `θ M : (F₁.obj M ⟶ Z₁) ⟶ (F₂.obj M ⟶ Z₂)`

is given, bijective at `P` and at `N`, and suppose the image of the cofork under `F₂` is a
cokernel.  Then morphisms out of `F₁.obj P` into `Z₁` killing `F₁.map a` factor uniquely through
`F₁.map b`: the image of the cofork under `F₁` has the universal property of a cokernel *at the
object `Z₁`*.

Quantifying that conclusion over `Z₁` turns it into a colimit, which is
`CategoryTheory.Limits.isColimitCokernelCoforkOfExistsUnique`.  The two statements are separated
because the family `θ` in the applications is built from a fixed `Z₁` — it is composition with an
`f`-map, whose target `Z₂` is the pushforward of `Z₁` — so the bijectivity hypotheses are
available one `Z₁` at a time.

## Main results

* `CategoryTheory.Limits.existsUnique_comp_of_bijective` — **the factorisation at a single test
  object**, from bijectivity of the family at the two sources of the cofork and the cokernel
  property downstairs.
* `CategoryTheory.Limits.isColimitCokernelCoforkOfExistsUnique` — a cofork with the unique
  factorisation property at every test object is a cokernel.
* `CategoryTheory.Limits.isColimitCokernelCoforkOfDescent` — **a cofork which is identified with
  the image of a cofork under a full and faithful functor preserving finite colimits is a cokernel
  as soon as it has the unique factorisation property at the test objects in the image of that
  functor.**  This is what upgrades the factorisation property from those test objects to all of
  them.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

variable {D : Type*} [Category* D] [HasZeroMorphisms D]

/-- **A cofork with the unique factorisation property at every test object is a cokernel.**  This
is `CategoryTheory.Limits.CokernelCofork.IsColimit.ofπ` with the descent, its factorisation and
its uniqueness all read off a proof of unique existence. -/
noncomputable def isColimitCokernelCoforkOfExistsUnique {Q P N : D} {a : Q ⟶ P} {b : P ⟶ N}
    (hab : a ≫ b = 0)
    (h : ∀ (Z : D) (k : P ⟶ Z), a ≫ k = 0 → ∃! m : N ⟶ Z, b ≫ m = k) :
    IsColimit (CokernelCofork.ofπ b hab) :=
  CokernelCofork.IsColimit.ofπ _ _ (fun {Z} k hk ↦ (h Z k hk).choose)
    (fun {Z} k hk ↦ (h Z k hk).choose_spec.1)
    (fun {Z} k hk m hm ↦ (h Z k hk).choose_spec.2 m hm)

variable {𝒜 : Type*} [Category* 𝒜] {ℬ₁ : Type*} [Category* ℬ₁] [HasZeroMorphisms ℬ₁]
  {ℬ₂ : Type*} [Category* ℬ₂] [HasZeroMorphisms ℬ₂]
  {F₁ : 𝒜 ⥤ ℬ₁} {F₂ : 𝒜 ⥤ ℬ₂} {Z₁ : ℬ₁} {Z₂ : ℬ₂}
  {θ : ∀ M : 𝒜, (F₁.obj M ⟶ Z₁) → (F₂.obj M ⟶ Z₂)}

/-- **A morphism out of the image of the middle term of a cofork, killing the image of the first,
factors uniquely through the image of the second** — provided a natural family of maps `θ` into
morphisms over the second functor is bijective at the middle and the last term, vanishes at the
zero morphism out of the first, and the image of the cofork under the second functor is a
cokernel.

The naturality hypothesis is the one
`CategoryTheory.Limits.isColimitCokernelCoforkOfExistsUnique`'s companions in
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.PresentedCrystal` use: `θ` turns
precomposition with the image of a morphism of `𝒜` under `F₁` into precomposition with its image
under `F₂`. -/
theorem existsUnique_comp_of_bijective
    (hθ : ∀ {M M' : 𝒜} (ψ : M ⟶ M') (k : F₁.obj M' ⟶ Z₁),
      θ M (F₁.map ψ ≫ k) = F₂.map ψ ≫ θ M' k)
    {Q P N : 𝒜} {a : Q ⟶ P} {b : P ⟶ N} {w₂ : F₂.map a ≫ F₂.map b = 0}
    (h₂ : IsColimit (CokernelCofork.ofπ (F₂.map b) w₂)) (hzero : θ Q 0 = 0)
    (hP : Function.Bijective (θ P)) (hN : Function.Bijective (θ N))
    (k : F₁.obj P ⟶ Z₁) (hk : F₁.map a ≫ k = 0) :
    ∃! m : F₁.obj N ⟶ Z₁, F₁.map b ≫ m = k := by
  have hak : F₂.map a ≫ θ P k = 0 := by rw [← hθ a k, hk, hzero]
  have hdesc : F₂.map b ≫ h₂.desc (CokernelCofork.ofπ (θ P k) hak) = θ P k := by
    simpa using Cofork.IsColimit.π_desc (t := CokernelCofork.ofπ (θ P k) hak) h₂
  obtain ⟨m, hm⟩ := hN.2 (h₂.desc (CokernelCofork.ofπ (θ P k) hak))
  have hbm : F₁.map b ≫ m = k := by
    refine hP.1 ?_
    rw [hθ b m, hm, hdesc]
  refine ⟨m, hbm, fun m' hm' ↦ ?_⟩
  have he₂ : Epi (F₂.map b) := by simpa using Cofork.IsColimit.epi h₂
  refine hN.1 ((cancel_epi (F₂.map b)).1 ?_)
  rw [← hθ b m', ← hθ b m, hm', hbm]

/-- **A cofork identified with the image of a cofork under a full and faithful functor preserving
finite colimits is a cokernel as soon as it has the unique factorisation property at the test
objects in the image of that functor.**

The three isomorphisms `eQ`, `eP`, `eN` identify the cofork `a`, `b` with the image of the cofork
`α₀`, `β₀`; the factorisation property at the test objects `T.obj Z` makes `β₀` a cokernel of
`α₀`, because the functor is fully faithful and so those test objects are exactly the ones the
universal property of `β₀` quantifies over; and preservation of finite colimits carries that
cokernel to one of the image, hence of the given cofork, against *every* test object. -/
noncomputable def isColimitCokernelCoforkOfDescent {D : Type*} [Category* D] [HasZeroMorphisms D]
    {E : Type*} [Category* E] [HasZeroMorphisms E] (T : D ⥤ E) [T.Full] [T.Faithful]
    [T.PreservesZeroMorphisms] [PreservesFiniteColimits T] {Q₀ P₀ N₀ : D} {Q P N : E}
    (eQ : Q ≅ T.obj Q₀) (eP : P ≅ T.obj P₀) (eN : N ≅ T.obj N₀) {α₀ : Q₀ ⟶ P₀} {β₀ : P₀ ⟶ N₀}
    {a : Q ⟶ P} {b : P ⟶ N} (hab : a ≫ b = 0)
    (hα : T.map α₀ = eQ.inv ≫ a ≫ eP.hom) (hβ : T.map β₀ = eP.inv ≫ b ≫ eN.hom)
    (h : ∀ (Z : D) (k : P ⟶ T.obj Z), a ≫ k = 0 → ∃! m : N ⟶ T.obj Z, b ≫ m = k) :
    IsColimit (CokernelCofork.ofπ b hab) := by
  have ha' : a ≫ eP.hom = eQ.hom ≫ T.map α₀ := by
    rw [hα]
    exact (Iso.hom_inv_id_assoc eQ _).symm
  have hb' : eP.hom ≫ T.map β₀ = b ≫ eN.hom := by
    rw [hβ]
    exact Iso.hom_inv_id_assoc eP _
  have hTαβ : T.map α₀ ≫ T.map β₀ = 0 := by
    refine (cancel_epi eQ.hom).1 ?_
    rw [comp_zero, ← Category.assoc, ← ha', Category.assoc, hb', ← Category.assoc, hab, zero_comp]
  have hαβ : α₀ ≫ β₀ = 0 := T.map_injective (by rw [T.map_comp, hTαβ, T.map_zero])
  have hβ₀ : IsColimit (CokernelCofork.ofπ β₀ hαβ) := by
    refine isColimitCokernelCoforkOfExistsUnique hαβ fun Z k hk ↦ ?_
    have hk' : a ≫ eP.hom ≫ T.map k = 0 := by
      rw [← Category.assoc, ha', Category.assoc, ← T.map_comp, hk, T.map_zero, comp_zero]
    obtain ⟨m', hm', hm'uniq⟩ := h Z (eP.hom ≫ T.map k) hk'
    refine ⟨T.preimage (eN.inv ≫ m'), ?_, fun m₁ hm₁ ↦ ?_⟩
    · refine T.map_injective ?_
      rw [T.map_comp, T.map_preimage]
      refine (cancel_epi eP.hom).1 ?_
      rw [← Category.assoc, hb', Category.assoc, Iso.hom_inv_id_assoc, hm']
    · refine T.map_injective ?_
      rw [T.map_preimage]
      have huniq : eN.hom ≫ T.map m₁ = m' := by
        refine hm'uniq (eN.hom ≫ T.map m₁) ?_
        change b ≫ eN.hom ≫ T.map m₁ = eP.hom ≫ T.map k
        rw [← Category.assoc, ← hb', Category.assoc, ← T.map_comp, hm₁]
      rw [← huniq, Iso.inv_hom_id_assoc]
  have hTβ : IsColimit (CokernelCofork.ofπ (T.map β₀) hTαβ) :=
    isColimitCoforkMapOfIsColimit' T hαβ hβ₀
  refine isColimitCokernelCoforkOfExistsUnique hab fun W k hk ↦ ?_
  have hg : T.map α₀ ≫ eP.inv ≫ k = 0 := by
    rw [hα, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, hk, comp_zero]
  have hfac : T.map β₀ ≫ hTβ.desc (CokernelCofork.ofπ (eP.inv ≫ k) hg) = eP.inv ≫ k := by
    simpa using Cofork.IsColimit.π_desc (t := CokernelCofork.ofπ (eP.inv ≫ k) hg) hTβ
  refine ⟨eN.hom ≫ hTβ.desc (CokernelCofork.ofπ (eP.inv ≫ k) hg), ?_, fun m₁ hm₁ ↦ ?_⟩
  · change b ≫ eN.hom ≫ hTβ.desc (CokernelCofork.ofπ (eP.inv ≫ k) hg) = k
    rw [← Category.assoc, ← hb', Category.assoc, hfac, Iso.hom_inv_id_assoc]
  · have h₁ : T.map β₀ ≫ eN.inv ≫ m₁ = eP.inv ≫ k := by
      refine (cancel_epi eP.hom).1 ?_
      rw [← Category.assoc, hb', Category.assoc, Iso.hom_inv_id_assoc, hm₁,
        Iso.hom_inv_id_assoc]
    have h₂ : eN.inv ≫ m₁ = hTβ.desc (CokernelCofork.ofπ (eP.inv ≫ k) hg) := by
      refine Cofork.IsColimit.hom_ext hTβ ?_
      simp only [Cofork.π_ofπ]
      rw [h₁, hfac]
    rw [← h₂, Iso.hom_inv_id_assoc]

end CategoryTheory.Limits

end
