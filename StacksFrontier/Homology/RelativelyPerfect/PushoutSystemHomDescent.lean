module

public import StacksFrontier.Homology.RelativelyPerfect.ColimitHom
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsSelfIso
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp

@[expose] public noncomputable section

/-!
# The morphism half of Stacks 0DHX for a system of pushouts

Let `R₀ → A₀` be flat of finite presentation, let `j ↦ Rⱼ` be a directed system of rings under
`R₀` with colimit `R∞`, and let `j ↦ Sⱼ` be a system of rings, `Sⱼ` a pushout of `Rⱼ ← R₀ → A₀`
and `S∞` a pushout of `R∞ ← R₀ → A₀`.  For `M ∈ D(A₀)` pseudo-coherent and `N ∈ D(A₀)` of finite
Tor dimension over `R₀`, write `E f` for derived extension of scalars along a ring map `f`.  This
file proves the two elementary halves of the bijectivity of
`colim_j Hom_{D(Sⱼ)}(E aⱼ M, E aⱼ N) ⟶ Hom_{D(S∞)}(E a∞ M, E a∞ N)`:

* a morphism at a stage which becomes zero over `S∞` is already zero at a later stage, and
* every morphism over `S∞` is the extension of scalars of a morphism at some stage, read through
  the composition isomorphism `E ι_j ∘ E a_j ≅ E a∞`.

This is Stacks 0DHX (`PseudoCoherence.relativelyPerfectComplexes_filteredColimit`, in the form
`PseudoCoherence.stageDerivedHom_descent`) for the stage algebras `Rⱼ ⊗[R₀] A₀`, transported along
two kinds of isomorphisms: the lift of `A₀` to its own universe which 0DHX applies before extending
scalars, and the identifications of the pushouts `Sⱼ` with the stage algebras.  Both transports use
only the cocycle condition `totalDerivedExtensionScalarsComp_assoc`.

## Main definitions

* `PseudoCoherence.PushoutSystem.extComp`: the composition isomorphism
  `E f ⋙ E g ≅ E c` of derived extension of scalars along a factorization `f ≫ g = c` in
  `CommRingCat`.
* `PseudoCoherence.PushoutSystem.VanishingDescent` and
  `PseudoCoherence.PushoutSystem.SurjectiveDescent`: the two halves above for an abstract system.

## Main results

* `PseudoCoherence.PushoutSystem.PushoutSystemData.vanishingDescent_of_isPushout` and
  `PseudoCoherence.PushoutSystem.PushoutSystemData.surjectiveDescent_of_isPushout`: the two halves
  for a system of pushouts, packaged as `PseudoCoherence.PushoutSystem.PushoutSystemData`.
* `PseudoCoherence.PushoutSystem.vanishingDescent_of_ringEquiv`,
  `surjectiveDescent_of_ringEquiv`, `vanishingDescent_of_iso` and `surjectiveDescent_of_iso`: the
  two halves transport along an isomorphism of base rings and along isomorphisms of the stage
  rings.
* `PseudoCoherence.PushoutSystem.derivedExtensionScalarsComp_eq`: the composition isomorphism of
  `StacksFrontier.Homology.RelativelyPerfect.ColimitHom` is `totalDerivedExtensionScalarsComp`.

## References

* [The Stacks Project, Tag 0DHX](https://stacks.math.columbia.edu/tag/0DHX)
-/

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open StacksDraft.TorAmplitude
open scoped TensorProduct

namespace PseudoCoherence.PushoutSystem

universe u

/- Derived extension of scalars and Stacks 0DHX are stated for the standard model of the derived
category of modules over a ring, so the declarations below are stated at it too. -/
attribute [local instance] HasDerivedCategory.standard

/-! ### Derived extension of scalars along morphisms of `CommRingCat` -/

/-- Derived extension of scalars along a morphism of commutative rings. -/
abbrev ext {A B : CommRingCat.{u}} (f : A ⟶ B) :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} B) :=
  (totalDerivedExtensionScalars.{u, u, u} f.hom).functor

/-- **The composition isomorphism along a factorization** `f ≫ g = c`: the composition isomorphism
`totalDerivedExtensionScalarsComp` followed by the transport along the factorization. -/
def extComp {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C) (c : A ⟶ C) (h : f ≫ g = c) :
    ext f ⋙ ext g ≅ ext c :=
  totalDerivedExtensionScalarsComp.{u, u} f.hom g.hom ≪≫
    eqToIso (congrArg (fun φ : A →+* C => (totalDerivedExtensionScalars.{u, u, u} φ).functor)
      (by rw [← h]; rfl))

/-- The components of `extComp`. -/
theorem extComp_hom_app {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C) (c : A ⟶ C)
    (h : f ≫ g = c) (X : DerivedCategory (ModuleCat.{u} A)) :
    (extComp f g c h).hom.app X =
      (totalDerivedExtensionScalarsComp.{u, u} f.hom g.hom).hom.app X ≫
        eqToHom (by subst h; rfl) := by
  subst h
  simp [extComp]

/-- `extComp` along a literal composite is `totalDerivedExtensionScalarsComp`. -/
theorem extComp_hom_app_comp {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (h : f ≫ g = f ≫ g) (X : DerivedCategory (ModuleCat.{u} A)) :
    (extComp f g (f ≫ g) h).hom.app X =
      (totalDerivedExtensionScalarsComp.{u, u} f.hom g.hom).hom.app X := by
  rw [extComp_hom_app]
  exact Category.comp_id _

/-- **The cocycle condition for `extComp`.** -/
theorem extComp_assoc {A B C D : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (fg : A ⟶ C) (gh : B ⟶ D) (fgh : A ⟶ D) (h₁ : f ≫ g = fg) (h₂ : g ≫ h = gh)
    (h₃ : fg ≫ h = fgh) (h₄ : f ≫ gh = fgh) (X : DerivedCategory (ModuleCat.{u} A)) :
    (ext h).map ((extComp f g fg h₁).hom.app X) ≫ (extComp fg h fgh h₃).hom.app X =
      (extComp g h gh h₂).hom.app ((ext f).obj X) ≫ (extComp f gh fgh h₄).hom.app X := by
  subst h₁ h₂ h₃
  rw [extComp_hom_app_comp, extComp_hom_app_comp, extComp_hom_app_comp, extComp_hom_app]
  exact (totalDerivedExtensionScalarsComp_assoc.{u, u} f.hom g.hom h.hom X).trans
    (congrArg _ (Category.comp_id _).symm)

/-- A morphism becomes zero after two extensions of scalars exactly when it becomes zero after
extension of scalars along the composite. -/
theorem ext_map_ext_map_eq_zero_iff {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (c : A ⟶ C) (h : f ≫ g = c) {X Y : DerivedCategory (ModuleCat.{u} A)} (φ : X ⟶ Y) :
    (ext g).map ((ext f).map φ) = 0 ↔ (ext c).map φ = 0 := by
  have hn := (extComp f g c h).hom.naturality φ
  dsimp at hn
  constructor
  · intro h0
    rw [h0, zero_comp] at hn
    have := congrArg (fun t => (extComp f g c h).inv.app X ≫ t) hn
    simpa using this.symm
  · intro h0
    rw [h0, comp_zero] at hn
    have := congrArg (fun t => t ≫ (extComp f g c h).inv.app Y) hn
    simpa using this

/-- A conjugate of a morphism by isomorphisms becomes zero after extension of scalars exactly
when the morphism does. -/
theorem ext_map_conj_eq_zero_iff {A B : CommRingCat.{u}} (f : A ⟶ B)
    {X X' Y Y' : DerivedCategory (ModuleCat.{u} A)} (e : X ≅ X') (e' : Y ≅ Y') (φ : X' ⟶ Y') :
    (ext f).map (e.hom ≫ φ ≫ e'.inv) = 0 ↔ (ext f).map φ = 0 := by
  constructor
  · intro h0
    have : (ext f).map φ = (ext f).map e.inv ≫ (ext f).map (e.hom ≫ φ ≫ e'.inv) ≫
        (ext f).map e'.hom := by
      simp only [← Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id,
        Iso.inv_hom_id_assoc]
    rw [this, h0, zero_comp, comp_zero]
  · intro h0
    simp only [Functor.map_comp, h0, zero_comp, comp_zero]

/-- Extension of scalars along an isomorphism of rings is fully faithful: extension of scalars
along the inverse is a quasi-inverse, by the composition and unit isomorphisms. -/
def extFullyFaithfulOfIso {A B : CommRingCat.{u}} (σ : A ≅ B) : (ext σ.hom).FullyFaithful :=
  (CategoryTheory.Equivalence.mk (ext σ.hom) (ext σ.inv)
    (totalDerivedExtensionScalarsId.{u, u} A ≪≫ (extComp σ.hom σ.inv (𝟙 A) σ.hom_inv_id).symm)
    (extComp σ.inv σ.hom (𝟙 B) σ.inv_hom_id ≪≫
      (totalDerivedExtensionScalarsId.{u, u} B).symm)).fullyFaithfulFunctor

/-! ### The two halves of the morphism assertion for an abstract system -/

section Abstract

variable {J : Type u} [Preorder J]

/-- **Vanishing descent**: a morphism between the extensions of scalars of `K` and `N` to a stage
which becomes zero over the colimit becomes zero at a later stage. -/
def VanishingDescent {A Sinf : CommRingCat.{u}} (S : J → CommRingCat.{u}) (a : ∀ j, A ⟶ S j)
    (t : ∀ {j k : J}, j ≤ k → (S j ⟶ S k)) (ι : ∀ j, S j ⟶ Sinf)
    (K N : DerivedCategory (ModuleCat.{u} A)) : Prop :=
  ∀ (j : J) (x : (ext (a j)).obj K ⟶ (ext (a j)).obj N), (ext (ι j)).map x = 0 →
    ∃ (k : J) (h : j ≤ k), (ext (t h)).map x = 0

/-- **Surjective descent**: every morphism between the extensions of scalars of `K` and `N` over
the colimit is, read through the composition isomorphism, the extension of scalars of a morphism
at some stage. -/
def SurjectiveDescent {A Sinf : CommRingCat.{u}} (S : J → CommRingCat.{u}) (a : ∀ j, A ⟶ S j)
    (ι : ∀ j, S j ⟶ Sinf) (ainf : A ⟶ Sinf) (hι : ∀ j, a j ≫ ι j = ainf)
    (K N : DerivedCategory (ModuleCat.{u} A)) : Prop :=
  ∀ y : (ext ainf).obj K ⟶ (ext ainf).obj N,
    ∃ (j : J) (x : (ext (a j)).obj K ⟶ (ext (a j)).obj N),
      (extComp (a j) (ι j) ainf (hι j)).inv.app K ≫ (ext (ι j)).map x ≫
        (extComp (a j) (ι j) ainf (hι j)).hom.app N = y

/-! #### Change of base ring along an isomorphism -/

section BaseChange

variable {A' A Sinf : CommRingCat.{u}} (e : A' ≃+* A) (S : J → CommRingCat.{u})
  (a' : ∀ j, A' ⟶ S j) (a : ∀ j, A ⟶ S j)
  (ha : ∀ j, CommRingCat.ofHom e.toRingHom ≫ a j = a' j)
  (t : ∀ {j k : J}, j ≤ k → (S j ⟶ S k)) (ι : ∀ j, S j ⟶ Sinf)

/-- Restriction of scalars along `e`, on derived categories. -/
abbrev restr : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A') :=
  (ModuleCat.restrictScalars.{u} e.toRingHom).mapDerivedCategory

/-- The identification `E(a'ⱼ)(e^* X) ≅ E(aⱼ)(X)`. -/
def baseChangeIso {B : CommRingCat.{u}} (b' : A' ⟶ B) (b : A ⟶ B)
    (hb : CommRingCat.ofHom e.toRingHom ≫ b = b') (X : DerivedCategory (ModuleCat.{u} A)) :
    (ext b').obj ((restr e).obj X) ≅ (ext b).obj X :=
  (extComp (CommRingCat.ofHom e.toRingHom) b b' hb).symm.app ((restr e).obj X) ≪≫
    (ext b).mapIso ((totalDerivedRestrictExtendScalarsSelfIso.{u, u} e).app X)

/-- The identifications `baseChangeIso` are compatible with a further extension of scalars. -/
theorem baseChangeIso_comp {B C : CommRingCat.{u}} (b' : A' ⟶ B) (b : A ⟶ B)
    (hb : CommRingCat.ofHom e.toRingHom ≫ b = b') (g : B ⟶ C) (c' : A' ⟶ C) (c : A ⟶ C)
    (hc : CommRingCat.ofHom e.toRingHom ≫ c = c') (hg' : b' ≫ g = c') (hg : b ≫ g = c)
    (X : DerivedCategory (ModuleCat.{u} A)) :
    (extComp b' g c' hg').app ((restr e).obj X) ≪≫ baseChangeIso e c' c hc X =
      (ext g).mapIso (baseChangeIso e b' b hb X) ≪≫ (extComp b g c hg).app X := by
  ext
  have hassoc := extComp_assoc (CommRingCat.ofHom e.toRingHom) b g b' c c' hb hg hg' hc
    ((restr e).obj X)
  have hnat : (ext g).map ((ext b).map
        ((totalDerivedRestrictExtendScalarsSelfIso.{u, u} e).hom.app X)) ≫
        (extComp b g c hg).hom.app X =
      (extComp b g c hg).hom.app ((ext (CommRingCat.ofHom e.toRingHom)).obj ((restr e).obj X)) ≫
        (ext c).map ((totalDerivedRestrictExtendScalarsSelfIso.{u, u} e).hom.app X) :=
    (extComp b g c hg).hom.naturality _
  simp only [baseChangeIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [hnat]
  simp only [← Category.assoc]
  congr 1
  rw [← cancel_mono ((extComp (CommRingCat.ofHom e.toRingHom) c c' hc).hom.app ((restr e).obj X))]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← hassoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]

include ha in
/-- Vanishing descent transports along an isomorphism of base rings. -/
theorem vanishingDescent_of_ringEquiv (K N : DerivedCategory (ModuleCat.{u} A))
    (h : VanishingDescent S a' t ι ((restr e).obj K) ((restr e).obj N)) :
    VanishingDescent S a t ι K N := by
  intro j x hx
  let θK := baseChangeIso e (a' j) (a j) (ha j) K
  let θN := baseChangeIso e (a' j) (a j) (ha j) N
  obtain ⟨k, hjk, hk⟩ := h j (θK.hom ≫ x ≫ θN.inv)
    ((ext_map_conj_eq_zero_iff (ι j) θK θN x).2 hx)
  exact ⟨k, hjk, (ext_map_conj_eq_zero_iff (t hjk) θK θN x).1 hk⟩

omit [Preorder J] in
include ha in
/-- Surjective descent transports along an isomorphism of base rings. -/
theorem surjectiveDescent_of_ringEquiv (ainf' : A' ⟶ Sinf) (ainf : A ⟶ Sinf)
    (hinf : CommRingCat.ofHom e.toRingHom ≫ ainf = ainf')
    (hι' : ∀ j, a' j ≫ ι j = ainf') (hι : ∀ j, a j ≫ ι j = ainf)
    (K N : DerivedCategory (ModuleCat.{u} A))
    (h : SurjectiveDescent S a' ι ainf' hι' ((restr e).obj K) ((restr e).obj N)) :
    SurjectiveDescent S a ι ainf hι K N := by
  intro y
  let θ := fun X => baseChangeIso e ainf' ainf hinf X
  obtain ⟨j, x', hx'⟩ := h ((θ K).hom ≫ y ≫ (θ N).inv)
  let φ := fun X => baseChangeIso e (a' j) (a j) (ha j) X
  refine ⟨j, (φ K).inv ≫ x' ≫ (φ N).hom, ?_⟩
  have hcoh := fun X => baseChangeIso_comp e (a' j) (a j) (ha j) (ι j) ainf' ainf hinf
    (hι' j) (hι j) X
  have hK := congrArg Iso.inv (hcoh K)
  have hN := congrArg Iso.hom (hcoh N)
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.app_inv, Iso.app_hom, Functor.mapIso_inv,
    Functor.mapIso_hom] at hK hN
  have hy : y = (θ K).inv ≫ ((θ K).hom ≫ y ≫ (θ N).inv) ≫ (θ N).hom := by simp
  rw [hy, ← hx']
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hK, hN]

end BaseChange

/-! #### Change of the stage rings along isomorphisms -/

section StageChange

variable {A Sinf Sinf' : CommRingCat.{u}} (S S' : J → CommRingCat.{u})
  (σ : ∀ j, S j ≅ S' j) (σinf : Sinf ≅ Sinf')
  (a : ∀ j, A ⟶ S j) (a' : ∀ j, A ⟶ S' j) (ha : ∀ j, a j ≫ (σ j).hom = a' j)
  (t : ∀ {j k : J}, j ≤ k → (S j ⟶ S k)) (t' : ∀ {j k : J}, j ≤ k → (S' j ⟶ S' k))
  (ht : ∀ {j k : J} (h : j ≤ k), t h ≫ (σ k).hom = (σ j).hom ≫ t' h)
  (ι : ∀ j, S j ⟶ Sinf) (ι' : ∀ j, S' j ⟶ Sinf')
  (hισ : ∀ j, ι j ≫ σinf.hom = (σ j).hom ≫ ι' j)

include ha ht hισ in
/-- Vanishing descent transports along isomorphisms of the stage rings. -/
theorem vanishingDescent_of_iso (K N : DerivedCategory (ModuleCat.{u} A))
    (h : VanishingDescent S a t ι K N) : VanishingDescent S' a' t' ι' K N := by
  intro j x' hx'
  let θ := fun X => (extComp (a j) (σ j).hom (a' j) (ha j)).app X
  let hF := extFullyFaithfulOfIso (σ j)
  let x := hF.preimage ((θ K).hom ≫ x' ≫ (θ N).inv)
  have hx : (ext (σ j).hom).map x = (θ K).hom ≫ x' ≫ (θ N).inv := hF.map_preimage _
  have h0 : (ext (ι j)).map x = 0 := by
    apply (extFullyFaithfulOfIso σinf).map_injective
    rw [Functor.map_zero, ext_map_ext_map_eq_zero_iff (ι j) σinf.hom _ rfl,
      ← ext_map_ext_map_eq_zero_iff (σ j).hom (ι' j) _ (hισ j).symm, hx]
    exact (ext_map_conj_eq_zero_iff (ι' j) (θ K) (θ N) x').2 hx'
  obtain ⟨k, hjk, hk⟩ := h j x h0
  refine ⟨k, hjk, ?_⟩
  have h1 : (ext (t' hjk)).map ((ext (σ j).hom).map x) = 0 := by
    rw [ext_map_ext_map_eq_zero_iff (σ j).hom (t' hjk) _ (ht hjk).symm,
      ← ext_map_ext_map_eq_zero_iff (t hjk) (σ k).hom _ rfl, hk, Functor.map_zero]
  rw [hx] at h1
  exact (ext_map_conj_eq_zero_iff (t' hjk) (θ K) (θ N) x').1 h1

/-- The isomorphism `E σ∞ ∘ E ιⱼ ≅ E ι'ⱼ ∘ E σⱼ` of a commutative square of ring maps. -/
def squareIso {B C B' C' : CommRingCat.{u}} (ιj : B ⟶ C) (σj : B ⟶ B') (σi : C ⟶ C')
    (ιj' : B' ⟶ C') (w : ιj ≫ σi = σj ≫ ιj') : ext ιj ⋙ ext σi ≅ ext σj ⋙ ext ιj' :=
  extComp ιj σi (ιj ≫ σi) rfl ≪≫ (extComp σj ιj' (ιj ≫ σi) w.symm).symm

omit [Preorder J] in
include ha hισ in
/-- Surjective descent transports along isomorphisms of the stage rings. -/
theorem surjectiveDescent_of_iso (ainf : A ⟶ Sinf) (ainf' : A ⟶ Sinf')
    (hinf : ainf ≫ σinf.hom = ainf') (hι : ∀ j, a j ≫ ι j = ainf)
    (hι' : ∀ j, a' j ≫ ι' j = ainf') (K N : DerivedCategory (ModuleCat.{u} A))
    (h : SurjectiveDescent S a ι ainf hι K N) : SurjectiveDescent S' a' ι' ainf' hι' K N := by
  intro y'
  let hFinf := extFullyFaithfulOfIso σinf
  obtain ⟨j, x, hx⟩ := h (hFinf.preimage ((extComp ainf σinf.hom ainf' hinf).hom.app K ≫ y' ≫
    (extComp ainf σinf.hom ainf' hinf).inv.app N))
  have hy : (ext σinf.hom).map ((extComp (a j) (ι j) ainf (hι j)).inv.app K ≫ (ext (ι j)).map x ≫
      (extComp (a j) (ι j) ainf (hι j)).hom.app N) =
      (extComp ainf σinf.hom ainf' hinf).hom.app K ≫ y' ≫
        (extComp ainf σinf.hom ainf' hinf).inv.app N := by
    rw [hx]
    exact hFinf.map_preimage _
  refine ⟨j, (extComp (a j) (σ j).hom (a' j) (ha j)).inv.app K ≫ (ext (σ j).hom).map x ≫
    (extComp (a j) (σ j).hom (a' j) (ha j)).hom.app N, ?_⟩
  have hcoh : ∀ X, (ext σinf.hom).map ((extComp (a j) (ι j) ainf (hι j)).hom.app X) ≫
      (extComp ainf σinf.hom ainf' hinf).hom.app X =
      (squareIso (ι j) (σ j).hom σinf.hom (ι' j) (hισ j)).hom.app ((ext (a j)).obj X) ≫
        (ext (ι' j)).map ((extComp (a j) (σ j).hom (a' j) (ha j)).hom.app X) ≫
          (extComp (a' j) (ι' j) ainf' (hι' j)).hom.app X := by
    intro X
    have h₁ := extComp_assoc (a j) (ι j) σinf.hom ainf (ι j ≫ σinf.hom) ainf' (hι j) rfl hinf
      (by rw [← Category.assoc, hι j, hinf]) X
    have h₂ := extComp_assoc (a j) (σ j).hom (ι' j) (a' j) (ι j ≫ σinf.hom) ainf' (ha j)
      (hισ j).symm (hι' j) (by rw [← Category.assoc, hι j, hinf]) X
    simp only [squareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
    rw [h₁, h₂, Iso.inv_hom_id_app_assoc]
  have hcohK := congrArg Iso.inv (show
      (ext σinf.hom).mapIso ((extComp (a j) (ι j) ainf (hι j)).app K) ≪≫
        (extComp ainf σinf.hom ainf' hinf).app K =
      (squareIso (ι j) (σ j).hom σinf.hom (ι' j) (hισ j)).app ((ext (a j)).obj K) ≪≫
        (ext (ι' j)).mapIso ((extComp (a j) (σ j).hom (a' j) (ha j)).app K) ≪≫
          (extComp (a' j) (ι' j) ainf' (hι' j)).app K from Iso.ext (hcoh K))
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] at hcohK
  have hnat : (ext σinf.hom).map ((ext (ι j)).map x) ≫
      (squareIso (ι j) (σ j).hom σinf.hom (ι' j) (hισ j)).hom.app ((ext (a j)).obj N) =
      (squareIso (ι j) (σ j).hom σinf.hom (ι' j) (hισ j)).hom.app ((ext (a j)).obj K) ≫
        (ext (ι' j)).map ((ext (σ j).hom).map x) :=
    (squareIso (ι j) (σ j).hom σinf.hom (ι' j) (hισ j)).hom.naturality x
  have hy' : y' = (extComp ainf σinf.hom ainf' hinf).inv.app K ≫
      (ext σinf.hom).map ((extComp (a j) (ι j) ainf (hι j)).inv.app K ≫ (ext (ι j)).map x ≫
        (extComp (a j) (ι j) ainf (hι j)).hom.app N) ≫
      (extComp ainf σinf.hom ainf' hinf).hom.app N := by
    rw [hy]
    simp
  rw [hy']
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hcohK, hcoh N, reassoc_of% hnat, Iso.inv_hom_id_app_assoc]

end StageChange

end Abstract

/-! ### The composition isomorphism of `ColimitHom` -/

/-- The composition isomorphism `PseudoCoherence.derivedExtensionScalarsComp` used to state the
morphism half of Stacks 0DHX is `totalDerivedExtensionScalarsComp`: both are characterized by the
same formula on complexes. -/
theorem derivedExtensionScalarsComp_eq {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    PseudoCoherence.derivedExtensionScalarsComp.{u, u} f g =
      totalDerivedExtensionScalarsComp.{u, u} f g :=
  Iso.ext (derivedExtensionScalarsCompHom_eq.{u, u} f g _ fun P =>
    (totalDerivedExtensionScalarsComp_comparison.{u, u} f g P).symm).symm

/-! ### Stacks 0DHX for the stage algebras, in the form of this file -/

section Stages

variable {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
  {R₀ : Type u} [CommRing R₀] (F : J ⥤ CommAlgCat.{u} R₀) (c : Cocone F)
  (hc : IsColimit ((CommAlgCat.uliftFunctor.{u, u, u} R₀).mapCocone c))
  (A₀ : Type u) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀]
  [Algebra.FinitePresentation R₀ A₀]

/-- The stage algebras `Rⱼ ⊗[R₀] A₀`. -/
abbrev stageRing (j : J) : CommRingCat.{u} := CommRingCat.of (stageAlgebra F A₀ j)

/-- The transition maps of the stage algebras. -/
abbrev stageTransition {j k : J} (h : j ≤ k) : stageRing F A₀ j ⟶ stageRing F A₀ k :=
  CommRingCat.ofHom (stageMap F A₀ (homOfLE h))

/-- The maps of the stage algebras to `R∞ ⊗[R₀] A₀`. -/
abbrev stageToLimit (j : J) : stageRing F A₀ j ⟶ CommRingCat.of (c.pt ⊗[R₀] A₀) :=
  CommRingCat.ofHom (stageToLimitMap c A₀ j)

omit [IsDirected J (· ≤ ·)] [Nonempty J] [Module.Flat R₀ A₀] [Algebra.FinitePresentation R₀ A₀] in
/-- The map `ULift A₀ → Rⱼ ⊗[R₀] A₀` followed by the map to `R∞ ⊗[R₀] A₀` is the map
`ULift A₀ → R∞ ⊗[R₀] A₀`. -/
theorem liftBaseToStage_comp_stageToLimit (j : J) :
    CommRingCat.ofHom (liftBaseToStageMap F A₀ j) ≫ stageToLimit F c A₀ j =
      CommRingCat.ofHom (liftBaseToLimitMap c A₀) :=
  CommRingCat.hom_ext (stageToLimitMap_comp_liftBaseToStageMap c A₀ j)

omit [IsDirected J (· ≤ ·)] [Nonempty J] [Module.Flat R₀ A₀] [Algebra.FinitePresentation R₀ A₀] in
/-- The map `A₀ → Rⱼ ⊗[R₀] A₀` followed by the map to `R∞ ⊗[R₀] A₀` is the map
`A₀ → R∞ ⊗[R₀] A₀`. -/
theorem baseToStage_comp_stageToLimit (j : J) :
    CommRingCat.ofHom (baseToStageMap F A₀ j) ≫ stageToLimit F c A₀ j =
      CommRingCat.ofHom (baseToLimitMap c A₀) := by
  ext a
  simp [stageToLimitMap, baseToStageMap, baseToLimitMap,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]

omit [IsDirected J (· ≤ ·)] [Nonempty J] [Module.Flat R₀ A₀] [Algebra.FinitePresentation R₀ A₀] in
/-- The limit composition isomorphism of `ColimitHom` is `extComp`. -/
theorem limitDerivedExtensionIso_eq (j : J) :
    limitDerivedExtensionIso c A₀ j =
      extComp (CommRingCat.ofHom (liftBaseToStageMap F A₀ j)) (stageToLimit F c A₀ j)
        (CommRingCat.ofHom (liftBaseToLimitMap c A₀))
        (liftBaseToStage_comp_stageToLimit F c A₀ j) := by
  rw [limitDerivedExtensionIso, derivedExtensionScalarsComp_eq]
  rfl

variable (K N : DerivedCategory (ModuleCat.{u} A₀))
  (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
  (hN : HasFiniteTorDimensionCanonical R₀
    ((ModuleCat.restrictScalars (algebraMap R₀ A₀)).mapDerivedCategory.obj N))

include hc hK hN in
/-- Vanishing descent for the stage algebras over the universe lift of `A₀`. -/
theorem vanishingDescent_stage :
    VanishingDescent (stageRing F A₀) (fun j => CommRingCat.ofHom (liftBaseToStageMap F A₀ j))
      (fun h => stageTransition F A₀ h) (stageToLimit F c A₀)
      ((baseLiftRestriction A₀).obj K) ((baseLiftRestriction A₀).obj N) := by
  intro j x hx
  have hx' : (totalDerivedExtensionScalars.{u, u, u} (stageToLimitMap c A₀ j)).functor.map x =
      (totalDerivedExtensionScalars.{u, u, u} (stageToLimitMap c A₀ j)).functor.map 0 :=
    hx.trans (Functor.map_zero _ _ _).symm
  have hcmp : stageDerivedHomComparison c A₀ j K N x = stageDerivedHomComparison c A₀ j K N 0 := by
    simp only [stageDerivedHomComparison]
    rw [hx']
  obtain ⟨k, f, hf⟩ := exists_stageDerivedHomTransition_eq F c hc A₀ K N hK hN j x 0 hcmp
  refine ⟨k, leOfHom f, ?_⟩
  simp only [stageDerivedHomTransition] at hf
  have h1 := (cancel_mono ((stageDerivedExtensionIso F A₀ f).hom.app _)).1
    ((cancel_epi ((stageDerivedExtensionIso F A₀ f).inv.app _)).1 hf)
  exact h1.trans (Functor.map_zero _ _ _)

include hc hK hN in
/-- Surjective descent for the stage algebras over the universe lift of `A₀`. -/
theorem surjectiveDescent_stage :
    SurjectiveDescent (stageRing F A₀) (fun j => CommRingCat.ofHom (liftBaseToStageMap F A₀ j))
      (stageToLimit F c A₀) (CommRingCat.ofHom (liftBaseToLimitMap c A₀))
      (liftBaseToStage_comp_stageToLimit F c A₀)
      ((baseLiftRestriction A₀).obj K) ((baseLiftRestriction A₀).obj N) := by
  intro y
  obtain ⟨j, φ, hφ⟩ := exists_stageDerivedHom F c hc A₀ K N hK hN y
  refine ⟨j, φ, ?_⟩
  rw [← hφ, stageDerivedHomComparison, limitDerivedExtensionIso_eq]
  rfl

end Stages

/-! ### A system of pushouts -/

section Pushouts

/-- **A directed system of pushouts.** For an `R₀`-algebra `A₀`, a system `j ↦ Rⱼ` of rings under
`R₀` with a cocone `R∞` under `R₀`, and a system `j ↦ Sⱼ` with a cocone `S∞`, where `Sⱼ` is a
pushout of `Rⱼ ← R₀ → A₀` and `S∞` a pushout of `R∞ ← R₀ → A₀`, compatibly. -/
structure PushoutSystemData (J : Type u) [Preorder J] (R₀ A₀ : CommRingCat.{u})
    [Algebra R₀ A₀] where
  /-- The system of rings `j ↦ Rⱼ`. -/
  R : J ⥤ CommRingCat.{u}
  /-- The maps `R₀ ⟶ Rⱼ`. -/
  r : ∀ j, R₀ ⟶ R.obj j
  /-- The maps `R₀ ⟶ Rⱼ` are compatible with the transitions. -/
  hr : ∀ {j k : J} (f : j ⟶ k), r j ≫ R.map f = r k
  /-- The cocone `R∞`. -/
  cR : Cocone R
  /-- The map `R₀ ⟶ R∞`. -/
  rinf : R₀ ⟶ cR.pt
  /-- The map `R₀ ⟶ R∞` is compatible with the legs. -/
  hrinf : ∀ j, r j ≫ cR.ι.app j = rinf
  /-- The system of pushouts `j ↦ Sⱼ`. -/
  S : J ⥤ CommRingCat.{u}
  /-- The cocone `S∞`. -/
  cS : Cocone S
  /-- The maps `A₀ ⟶ Sⱼ`. -/
  a : ∀ j, A₀ ⟶ S.obj j
  /-- The map `A₀ ⟶ S∞`. -/
  ainf : A₀ ⟶ cS.pt
  /-- The maps `Rⱼ ⟶ Sⱼ`. -/
  b : R ⟶ S
  /-- The map `R∞ ⟶ S∞`. -/
  binf : cR.pt ⟶ cS.pt
  /-- The maps `A₀ ⟶ Sⱼ` are compatible with the transitions. -/
  ha : ∀ {j k : J} (f : j ⟶ k), a j ≫ S.map f = a k
  /-- The maps `A₀ ⟶ Sⱼ` are compatible with the legs. -/
  haι : ∀ j, a j ≫ cS.ι.app j = ainf
  /-- The maps `Rⱼ ⟶ Sⱼ` are compatible with the legs. -/
  hbι : ∀ j, b.app j ≫ cS.ι.app j = cR.ι.app j ≫ binf
  /-- Each `Sⱼ` is the pushout of `Rⱼ ← R₀ → A₀`. -/
  isPushout : ∀ j, IsPushout (r j) (CommRingCat.ofHom (algebraMap R₀ A₀)) (b.app j) (a j)
  /-- `S∞` is the pushout of `R∞ ← R₀ → A₀`. -/
  isPushout_inf : IsPushout rinf (CommRingCat.ofHom (algebraMap R₀ A₀)) binf ainf

namespace PushoutSystemData

variable {J : Type u} [Preorder J] {R₀ A₀ : CommRingCat.{u}} [Algebra R₀ A₀]
  (P : PushoutSystemData J R₀ A₀)

/-- The system `j ↦ Rⱼ` as a diagram of rings under `R₀`. -/
def underDiagram : J ⥤ Under R₀ where
  obj j := Under.mk (P.r j)
  map f := Under.homMk (P.R.map f) (P.hr f)
  map_id j := by ext; simp
  map_comp f g := by ext; simp

/-- The cocone `R∞` as a cocone of rings under `R₀`. -/
def underCocone : Cocone P.underDiagram where
  pt := Under.mk P.rinf
  ι :=
    { app j := Under.homMk (P.cR.ι.app j) (P.hrinf j)
      naturality {j k} f := by ext; simp [underDiagram] }

/-- The system `j ↦ Rⱼ` as a diagram of `R₀`-algebras. -/
def algDiagram : J ⥤ CommAlgCat.{u} R₀ :=
  P.underDiagram ⋙ (commAlgCatEquivUnder R₀).inverse

/-- The cocone `R∞` as a cocone of `R₀`-algebras. -/
def algCocone : Cocone P.algDiagram :=
  (commAlgCatEquivUnder R₀).inverse.mapCocone P.underCocone

/-- The transition maps of `algDiagram` are those of the ring system `j ↦ Rⱼ`. -/
theorem algDiagram_map_hom_apply {j k : J} (f : j ⟶ k) (x : P.algDiagram.obj j) :
    (P.algDiagram.map f).hom x = (P.R.map f).hom x := rfl

/-- The legs of `algCocone` are those of the ring cocone `R∞`. -/
theorem algCocone_ι_hom_apply (j : J) (x : P.algDiagram.obj j) :
    (P.algCocone.ι.app j).hom x = (P.cR.ι.app j).hom x := rfl

/-- `R∞` is a colimit of `R₀`-algebras when it is a colimit of rings. -/
def isColimitAlgCocone [IsDirected J (· ≤ ·)] [Nonempty J] (hcR : IsColimit P.cR) :
    IsColimit P.algCocone := by
  have : IsConnected J := IsFiltered.isConnected J
  have h : IsColimit ((Under.forget R₀).mapCocone P.underCocone) := hcR
  exact isColimitOfPreserves _ (isColimitOfReflects (Under.forget R₀) h)

/-- The inclusion `Rⱼ ⟶ Rⱼ ⊗[R₀] A₀`. -/
abbrev stageInl (j : J) : P.R.obj j ⟶ stageRing P.algDiagram A₀ j :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R₀)
    (A := P.algDiagram.obj j) (B := A₀))

/-- The inclusion `R∞ ⟶ R∞ ⊗[R₀] A₀`. -/
abbrev limitInl : P.cR.pt ⟶ CommRingCat.of (P.algCocone.pt ⊗[R₀] A₀) :=
  CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R₀)
    (A := P.algCocone.pt) (B := A₀))

/-- The identification of the stage algebra `Rⱼ ⊗[R₀] A₀` with the pushout `Sⱼ`. -/
def stageIso (j : J) : stageRing P.algDiagram A₀ j ≅ P.S.obj j :=
  (CommRingCat.isPushout_tensorProduct R₀ (P.algDiagram.obj j) A₀).isoIsPushout _ _
    (P.isPushout j)

/-- The identification of `R∞ ⊗[R₀] A₀` with the pushout `S∞`. -/
def limitIso : CommRingCat.of (P.algCocone.pt ⊗[R₀] A₀) ≅ P.cS.pt :=
  (CommRingCat.isPushout_tensorProduct R₀ P.algCocone.pt A₀).isoIsPushout _ _ P.isPushout_inf

/-- The inclusion `Rⱼ ⟶ Rⱼ ⊗[R₀] A₀` followed by `stageIso` is the map `Rⱼ ⟶ Sⱼ`. -/
theorem stageInl_comp_stageIso (j : J) : P.stageInl j ≫ (P.stageIso j).hom = P.b.app j :=
  IsPushout.inl_isoIsPushout_hom _ _ _ _

/-- The map `A₀ ⟶ Rⱼ ⊗[R₀] A₀` followed by `stageIso` is the map `A₀ ⟶ Sⱼ`. -/
theorem baseToStage_comp_stageIso (j : J) :
    CommRingCat.ofHom (baseToStageMap P.algDiagram A₀ j) ≫ (P.stageIso j).hom = P.a j :=
  IsPushout.inr_isoIsPushout_hom _ _ _ _

/-- The inclusion `R∞ ⟶ R∞ ⊗[R₀] A₀` followed by `limitIso` is the map `R∞ ⟶ S∞`. -/
theorem limitInl_comp_limitIso : P.limitInl ≫ P.limitIso.hom = P.binf :=
  IsPushout.inl_isoIsPushout_hom _ _ _ _

/-- The map `A₀ ⟶ R∞ ⊗[R₀] A₀` followed by `limitIso` is the map `A₀ ⟶ S∞`. -/
theorem baseToLimit_comp_limitIso :
    CommRingCat.ofHom (baseToLimitMap P.algCocone A₀) ≫ P.limitIso.hom = P.ainf :=
  IsPushout.inr_isoIsPushout_hom _ _ _ _

/-- The isomorphisms `stageIso` commute with the transition maps of the stage algebras and of
the system `j ↦ Sⱼ`. -/
theorem stageTransition_comp_stageIso {j k : J} (h : j ≤ k) :
    stageTransition P.algDiagram A₀ h ≫ (P.stageIso k).hom =
      (P.stageIso j).hom ≫ P.S.map (homOfLE h) := by
  refine (CommRingCat.isPushout_tensorProduct R₀ (P.algDiagram.obj j) A₀).hom_ext ?_ ?_
  · have e₁ : P.stageInl j ≫ stageTransition P.algDiagram A₀ h =
        P.R.map (homOfLE h) ≫ P.stageInl k := by
      ext x
      simp only [CommRingCat.hom_comp, ConcreteCategory.hom_ofHom, stageMap, homOfLE_leOfHom,
        AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
      exact rfl
    change P.stageInl j ≫ _ ≫ _ = P.stageInl j ≫ _ ≫ _
    rw [reassoc_of% e₁, P.stageInl_comp_stageIso, ← Category.assoc, P.stageInl_comp_stageIso]
    exact P.b.naturality (homOfLE h)
  · have e₂ : CommRingCat.ofHom (baseToStageMap P.algDiagram A₀ j) ≫
        stageTransition P.algDiagram A₀ h =
          CommRingCat.ofHom (baseToStageMap P.algDiagram A₀ k) := by
      ext x
      simp [stageMap, baseToStageMap, Algebra.TensorProduct.map_tmul]
    change CommRingCat.ofHom (baseToStageMap P.algDiagram A₀ j) ≫ _ ≫ _ =
      CommRingCat.ofHom (baseToStageMap P.algDiagram A₀ j) ≫ _ ≫ _
    rw [reassoc_of% e₂, P.baseToStage_comp_stageIso, ← Category.assoc,
      P.baseToStage_comp_stageIso]
    exact (P.ha (homOfLE h)).symm

/-- The isomorphisms `stageIso` and `limitIso` commute with the maps `Rⱼ ⊗[R₀] A₀ ⟶ R∞ ⊗[R₀] A₀`
and the cocone maps `Sⱼ ⟶ S∞`. -/
theorem stageToLimit_comp_limitIso (j : J) :
    stageToLimit P.algDiagram P.algCocone A₀ j ≫ P.limitIso.hom =
      (P.stageIso j).hom ≫ P.cS.ι.app j := by
  refine (CommRingCat.isPushout_tensorProduct R₀ (P.algDiagram.obj j) A₀).hom_ext ?_ ?_
  · have e₁ : P.stageInl j ≫ stageToLimit P.algDiagram P.algCocone A₀ j =
        P.cR.ι.app j ≫ P.limitInl := by
      ext x
      simp only [CommRingCat.hom_comp, ConcreteCategory.hom_ofHom, stageToLimitMap,
        Functor.const_obj_obj, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
        Function.comp_apply]
      exact rfl
    change P.stageInl j ≫ _ ≫ _ = P.stageInl j ≫ _ ≫ _
    rw [reassoc_of% e₁, P.limitInl_comp_limitIso, ← Category.assoc, P.stageInl_comp_stageIso]
    exact (P.hbι j).symm
  · have e₂ := baseToStage_comp_stageToLimit P.algDiagram P.algCocone A₀ j
    change CommRingCat.ofHom (baseToStageMap P.algDiagram A₀ j) ≫ _ ≫ _ =
      CommRingCat.ofHom (baseToStageMap P.algDiagram A₀ j) ≫ _ ≫ _
    rw [reassoc_of% e₂, P.baseToLimit_comp_limitIso, ← Category.assoc, P.baseToStage_comp_stageIso]
    exact (P.haι j).symm

variable [IsDirected J (· ≤ ·)] [Nonempty J] (hcR : IsColimit P.cR) [Module.Flat R₀ A₀]
  [Algebra.FinitePresentation R₀ A₀] (M N : DerivedCategory (ModuleCat.{u} A₀))
  (hM : StacksDraft.PseudoCoherence.IsPseudoCoherent M)
  (hN : HasFiniteTorDimensionCanonical R₀
    ((ModuleCat.restrictScalars (algebraMap R₀ A₀)).mapDerivedCategory.obj N))

include hcR hM hN in
/-- **Stacks 0DHX, vanishing descent for a system of pushouts.** Let `R₀ → A₀` be flat of finite
presentation, `j ↦ Rⱼ` a directed system of rings under `R₀` with colimit `R∞`, and `Sⱼ`, `S∞`
pushouts of `Rⱼ ← R₀ → A₀` and `R∞ ← R₀ → A₀`.  For `M` pseudo-coherent and `N` of finite Tor
dimension over `R₀`, a morphism `E aⱼ M ⟶ E aⱼ N` which becomes zero over `S∞` becomes zero over
some `Sₖ`, `j ≤ k`. -/
theorem vanishingDescent_of_isPushout (j : J)
    (x : (ext (P.a j)).obj M ⟶ (ext (P.a j)).obj N) (hx : (ext (P.cS.ι.app j)).map x = 0) :
    ∃ (k : J) (h : j ≤ k), (ext (P.S.map (homOfLE h))).map x = 0 := by
  have hc := isColimit_mapCocone_commAlgCat_uliftFunctor (P.isColimitAlgCocone hcR)
  have h₁ := vanishingDescent_stage P.algDiagram P.algCocone hc A₀ M N hM hN
  have h₂ := vanishingDescent_of_ringEquiv (A' := CommRingCat.of (ULift.{u} A₀)) (A := A₀)
    (ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀) (stageRing P.algDiagram A₀) _
    (fun j => CommRingCat.ofHom (baseToStageMap P.algDiagram A₀ j)) (fun _ => rfl)
    (fun h => stageTransition P.algDiagram A₀ h) (stageToLimit P.algDiagram P.algCocone A₀) M N h₁
  exact vanishingDescent_of_iso _ (fun j => P.S.obj j) P.stageIso P.limitIso _ P.a
    P.baseToStage_comp_stageIso _ (fun h => P.S.map (homOfLE h))
    (fun h => P.stageTransition_comp_stageIso h) _ (fun j => P.cS.ι.app j)
    P.stageToLimit_comp_limitIso M N h₂ j x hx

include hcR hM hN in
/-- **Stacks 0DHX, surjective descent for a system of pushouts.** In the situation of
`vanishingDescent_of_isPushout`, every morphism `E a∞ M ⟶ E a∞ N` is, read through the
composition isomorphisms `E ιⱼ ∘ E aⱼ ≅ E a∞`, the extension of scalars of a morphism
`E aⱼ M ⟶ E aⱼ N` for some stage `j`. -/
theorem surjectiveDescent_of_isPushout (y : (ext P.ainf).obj M ⟶ (ext P.ainf).obj N) :
    ∃ (j : J) (x : (ext (P.a j)).obj M ⟶ (ext (P.a j)).obj N),
      (extComp (P.a j) (P.cS.ι.app j) P.ainf (P.haι j)).inv.app M ≫
          (ext (P.cS.ι.app j)).map x ≫
        (extComp (P.a j) (P.cS.ι.app j) P.ainf (P.haι j)).hom.app N = y := by
  have hc := isColimit_mapCocone_commAlgCat_uliftFunctor (P.isColimitAlgCocone hcR)
  have h₁ := surjectiveDescent_stage P.algDiagram P.algCocone hc A₀ M N hM hN
  have h₂ := surjectiveDescent_of_ringEquiv (A' := CommRingCat.of (ULift.{u} A₀)) (A := A₀)
    (ULift.ringEquiv : ULift.{u} A₀ ≃+* A₀) (stageRing P.algDiagram A₀) _
    (fun j => CommRingCat.ofHom (baseToStageMap P.algDiagram A₀ j)) (fun _ => rfl)
    (stageToLimit P.algDiagram P.algCocone A₀) _
    (CommRingCat.ofHom (baseToLimitMap P.algCocone A₀)) rfl
    (liftBaseToStage_comp_stageToLimit P.algDiagram P.algCocone A₀)
    (baseToStage_comp_stageToLimit P.algDiagram P.algCocone A₀) M N h₁
  exact surjectiveDescent_of_iso _ (fun j => P.S.obj j) P.stageIso P.limitIso _ P.a
    P.baseToStage_comp_stageIso _ (fun j => P.cS.ι.app j) P.stageToLimit_comp_limitIso _ P.ainf
    P.baseToLimit_comp_limitIso _ P.haι M N h₂ y

end PushoutSystemData

end Pushouts

end PseudoCoherence.PushoutSystem
