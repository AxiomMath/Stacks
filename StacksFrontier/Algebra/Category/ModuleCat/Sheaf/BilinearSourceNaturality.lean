module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearNaturality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison
public import StacksCore.Tactic.StacksAttribute

/-! # Naturality in the source of the bilinear-pairing bijections

The chain of bijections which proves Stacks 03EL compares morphisms out of `f^*(F ⊗ G)` with
morphisms out of `f^*F ⊗ f^*G` for a morphism of ringed topoi, and the comparison is asserted to
be natural in `F` and in `G`. `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearNaturality`
supplies the naturality of each link of that chain in the sheaf of *values*; this file supplies
the naturality in the two *source* modules, which is the other half of what the Yoneda step
needs.

Naturality in the source is with respect to precomposition. On the bilinear-pairing side the
operation is precomposition of a pairing with a product `prod.map (s) (t)` of the underlying
morphisms of sheaves of sets; on the tensor-product side it is precomposition with the
functorial image of `s ⊗ₘ t`. The two are matched by
`Stacks.SheafOfModules.tensorHomOfPairing_precomp`.

The file also records the two general tools the assembly of Tag 03EL runs on: the universal
property of the tensor product sheaf at the generality in which the inverse image of a structure
sheaf is available (a presheaf of commutative rings whose underlying presheaf of rings is a
sheaf, rather than a sheaf of commutative rings), and the fact that a family of hom-set
bijections natural in both variables is an isomorphism of functors.

## Main definitions

* `Stacks.SheafOfModules.tensorSheafHomEquivPresheafTensorHom` and
  `Stacks.SheafOfModules.bilinearEquivTensorSheafHom`: the universal property of the tensor
  product sheaf `Stacks.SheafOfModules.Tensor.sheafTensor`, i.e. `Hom_A(F ⊗_A G, N) =
    Bilin_A(F × G, N)`, for a
  presheaf of commutative rings `A` whose underlying presheaf of rings is a sheaf. These
  generalise `Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom` and
  `Stacks.SheafOfModules.bilinearEquivTensorHom`, which are stated for a sheaf of commutative
  rings; the two agree because
  `Stacks.SheafOfModules.commRingSheaf_eq_underlyingRingSheafOfSite` holds by definition.
* `CategoryTheory.Functor.natIsoOfHomEquiv`: two functors with a family of hom-set bijections
  natural in the source and in the target are isomorphic.

## Main results

* `Stacks.SheafOfModules.IsBilinearPairing.precomp`: a bilinear pairing precomposed with a
  product of morphisms of sheaves of modules is bilinear.
* `Stacks.SheafOfModules.tensorHomOfPairing_precomp`: the morphism out of the objectwise tensor
  product determined by a bilinear pairing is natural in the two source modules.
* `Stacks.SheafOfModules.bilinearEquivTensorSheafHom_naturality` and
  `Stacks.SheafOfModules.bilinearEquivTensorSheafHom_precomp`: the universal property of the
  tensor product sheaf is natural in the sheaf of values and in the two source modules.
* `Stacks.SheafOfModules.inverseImagePairingEquiv_precomp` and
  `Stacks.SheafOfModules.inverseImageBilinearEquiv_precomp`: the bijection between pairings of
  the inverse images and pairings into the direct image is natural in the two source modules.

## Implementation notes

`Stacks.SheafOfModules.inverseImagePairingEquiv_precomp` is proved in term mode. Its two sides
spell one object two ways — the source of the pairing upstairs is
`moduleSheaf _ ((inverseImageModules f O).obj F)` in the statement of
`Stacks.SheafOfModules.inverseImagePairingEquiv` and `f.inverseImage.obj (moduleSheaf O F)` in
its `@[simp]` characterisation — and the two are definitionally equal only at default
transparency, so `rw` reports "did not find an occurrence" on a pattern that is visibly present,
with Lean's own note that the goal is not type-correct at the `implicit` level. `congrArg` and
`Eq.trans` do the same work and type-check at default transparency.

For the same reason `Stacks.SheafOfModules.tensorSheafHomEquivPresheafTensorHom` is defined as
the hom-set bijection of `PresheafOfModules.sheafificationAdjunction` rather than as
`PresheafOfModules.sheafificationHomEquiv`: the two are definitionally equal, but only the
former lets `CategoryTheory.Adjunction.homEquiv_naturality_right_symm` and
`..._left_symm` be applied to it directly, and the inverse bijection is the direction the chain
of Tag 03EL traverses.

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

/-! ## Functors compared by a family of hom-set bijections -/

namespace CategoryTheory.Functor

universe v₂ u₂ v₁ u₁

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] {Φ Ψ : A ⥤ B}
  (e : ∀ (a : A) (N : B), (Φ.obj a ⟶ N) ≃ (Ψ.obj a ⟶ N))

/-- The natural transformation `Ψ ⟶ Φ` determined by a family of hom-set bijections natural in
the target and in the source: its component at `a` is the image of the identity of `Φ.obj a`. -/
def natTransOfHomEquiv
    (hN : ∀ (a : A) {N N' : B} (k : N ⟶ N') (g : Φ.obj a ⟶ N), e a N' (g ≫ k) = e a N g ≫ k)
    (hA : ∀ {a a' : A} (u : a ⟶ a') (N : B) (g : Φ.obj a' ⟶ N),
      e a N (Φ.map u ≫ g) = Ψ.map u ≫ e a' N g) :
    Ψ ⟶ Φ where
  app a := e a (Φ.obj a) (𝟙 (Φ.obj a))
  naturality a a' u := by
    have h₁ := hN a (Φ.map u) (𝟙 (Φ.obj a))
    have h₂ := hA u (Φ.obj a') (𝟙 (Φ.obj a'))
    rw [Category.id_comp] at h₁
    rw [Category.comp_id] at h₂
    exact h₂.symm.trans h₁

/-- Each component of `CategoryTheory.Functor.natTransOfHomEquiv` is an isomorphism: the
bijection at the target `Ψ.obj a` produces the inverse, and the naturality in the target alone
proves it is one. -/
lemma isIso_app_natTransOfHomEquiv
    (hN : ∀ (a : A) {N N' : B} (k : N ⟶ N') (g : Φ.obj a ⟶ N), e a N' (g ≫ k) = e a N g ≫ k)
    (hA : ∀ {a a' : A} (u : a ⟶ a') (N : B) (g : Φ.obj a' ⟶ N),
      e a N (Φ.map u ≫ g) = Ψ.map u ≫ e a' N g) (a : A) :
    IsIso ((natTransOfHomEquiv e hN hA).app a) := by
  refine ⟨(e a (Ψ.obj a)).symm (𝟙 (Ψ.obj a)), ?_, ?_⟩
  · have h := hN a ((e a (Ψ.obj a)).symm (𝟙 (Ψ.obj a))) (𝟙 (Φ.obj a))
    rw [Category.id_comp, Equiv.apply_symm_apply] at h
    exact h.symm
  · refine (e a (Φ.obj a)).injective ?_
    have h := hN a (e a (Φ.obj a) (𝟙 (Φ.obj a))) ((e a (Ψ.obj a)).symm (𝟙 (Ψ.obj a)))
    rw [Equiv.apply_symm_apply, Category.id_comp] at h
    exact h

/-- **A family of hom-set bijections natural in the source and in the target is an isomorphism
of functors.** This is the Yoneda step: the two functors corepresent the same functor of the
target, uniformly in the source. -/
def natIsoOfHomEquiv
    (hN : ∀ (a : A) {N N' : B} (k : N ⟶ N') (g : Φ.obj a ⟶ N), e a N' (g ≫ k) = e a N g ≫ k)
    (hA : ∀ {a a' : A} (u : a ⟶ a') (N : B) (g : Φ.obj a' ⟶ N),
      e a N (Φ.map u ≫ g) = Ψ.map u ≫ e a' N g) :
    Ψ ≅ Φ :=
  @asIso _ _ _ _ _ (@NatIso.isIso_of_isIso_app _ _ _ _ _ _ (natTransOfHomEquiv e hN hA)
    (isIso_app_natTransOfHomEquiv e hN hA))

/-- The component of `CategoryTheory.Functor.natTransOfHomEquiv` at `a`, followed by the
preimage of the identity of `Ψ.obj a`, is the identity. -/
lemma natTransOfHomEquiv_app_comp_symm_id
    (hN : ∀ (a : A) {N N' : B} (k : N ⟶ N') (g : Φ.obj a ⟶ N), e a N' (g ≫ k) = e a N g ≫ k)
    (hA : ∀ {a a' : A} (u : a ⟶ a') (N : B) (g : Φ.obj a' ⟶ N),
      e a N (Φ.map u ≫ g) = Ψ.map u ≫ e a' N g) (a : A) :
    (natTransOfHomEquiv e hN hA).app a ≫ (e a (Ψ.obj a)).symm (𝟙 (Ψ.obj a)) = 𝟙 (Ψ.obj a) := by
  have h := hN a ((e a (Ψ.obj a)).symm (𝟙 (Ψ.obj a))) (𝟙 (Φ.obj a))
  rw [Category.id_comp, Equiv.apply_symm_apply] at h
  exact h.symm

/-- The inverse of `CategoryTheory.Functor.natIsoOfHomEquiv` is the preimage of the identity:
the comparison `Φ.obj a ⟶ Ψ.obj a` is the morphism whose image under the bijection at the target
`Ψ.obj a` is the identity. This is the handle on the comparison that any statement pinning it
down on elements has to start from. -/
lemma natIsoOfHomEquiv_inv_app
    (hN : ∀ (a : A) {N N' : B} (k : N ⟶ N') (g : Φ.obj a ⟶ N), e a N' (g ≫ k) = e a N g ≫ k)
    (hA : ∀ {a a' : A} (u : a ⟶ a') (N : B) (g : Φ.obj a' ⟶ N),
      e a N (Φ.map u ≫ g) = Ψ.map u ≫ e a' N g) (a : A) :
    (natIsoOfHomEquiv e hN hA).inv.app a = (e a (Ψ.obj a)).symm (𝟙 (Ψ.obj a)) := by
  rw [← cancel_epi ((natIsoOfHomEquiv e hN hA).hom.app a), Iso.hom_inv_id_app]
  exact (natTransOfHomEquiv_app_comp_symm_id e hN hA a).symm

/-- The components of `CategoryTheory.Functor.natIsoOfHomEquiv` are the images of the
identities. -/
lemma natIsoOfHomEquiv_hom_app
    (hN : ∀ (a : A) {N N' : B} (k : N ⟶ N') (g : Φ.obj a ⟶ N), e a N' (g ≫ k) = e a N g ≫ k)
    (hA : ∀ {a a' : A} (u : a ⟶ a') (N : B) (g : Φ.obj a' ⟶ N),
      e a N (Φ.map u ≫ g) = Ψ.map u ≫ e a' N g) (a : A) :
    (natIsoOfHomEquiv e hN hA).hom.app a = e a (Φ.obj a) (𝟙 (Φ.obj a)) := rfl

end CategoryTheory.Functor

universe w v u

namespace Stacks.SheafOfModules

/-! ## Precomposition of a pairing with a product of morphisms -/

section Precomp

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {R : Sheaf J RingCat.{w}} {A A' B B' N : SheafOfModules.{w} R}

omit [J.HasSheafCompose (forget RingCat.{w})] in
/-- The value on a pair of local sections of a pairing precomposed with a product of morphisms
of sheaves of modules: apply the two morphisms to the two sections first. -/
lemma pairingApp_prodMap_comp (q : moduleSheaf R A' ⨯ moduleSheaf R B' ⟶ moduleSheaf R N)
    (s : A ⟶ A') (t : B ⟶ B') (U : Cᵒᵖ)
    (a : (sectionsFunctor J U).obj (moduleSheaf R A))
    (b : (sectionsFunctor J U).obj (moduleSheaf R B)) :
    pairingApp R (prod.map ((moduleSheafFunctor R).map s)
        ((moduleSheafFunctor R).map t) ≫ q) U a b =
      pairingApp R q U ((sectionsFunctor J U).map ((moduleSheafFunctor R).map s) a)
        ((sectionsFunctor J U).map ((moduleSheafFunctor R).map t) b) := by
  rw [pairingApp, (sectionsFunctor J U).map_comp_apply, Functor.map_prodMap_apply,
    Functor.map_fst_prodObjMk, Functor.map_snd_prodObjMk]
  rfl

/-- A bilinear pairing precomposed with a product of morphisms of sheaves of modules is
bilinear, because a morphism of sheaves of modules is additive and linear on sections. This is
the action of `Bilin_O(- × -, N)` on morphisms. -/
lemma IsBilinearPairing.precomp
    {q : moduleSheaf R A' ⨯ moduleSheaf R B' ⟶ moduleSheaf R N}
    (hq : IsBilinearPairing R q) (s : A ⟶ A') (t : B ⟶ B') :
    IsBilinearPairing R (prod.map ((moduleSheafFunctor R).map s)
      ((moduleSheafFunctor R).map t) ≫ q) where
  add_left U a a' b := by
    rw [pairingApp_prodMap_comp, pairingApp_prodMap_comp, pairingApp_prodMap_comp,
      sectionsFunctor_map_moduleSheafFunctor_map_add, hq.add_left]
  add_right U a b b' := by
    rw [pairingApp_prodMap_comp, pairingApp_prodMap_comp, pairingApp_prodMap_comp,
      sectionsFunctor_map_moduleSheafFunctor_map_add, hq.add_right]
  smul_left U r a b := by
    rw [pairingApp_prodMap_comp, pairingApp_prodMap_comp,
      sectionsFunctor_map_moduleSheafFunctor_map_smul, hq.smul_left]
  smul_right U r a b := by
    rw [pairingApp_prodMap_comp, pairingApp_prodMap_comp,
      sectionsFunctor_map_moduleSheafFunctor_map_smul, hq.smul_right]

end Precomp

/-! ## Naturality in the source of the presheaf-level universal property -/

section PresheafTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}} {hO : Presheaf.IsSheaf J
    (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf O)}
  {A A' B B' N : SheafOfModules.{w} (commRingSheaf J O hO)}

/-- **The universal property of the objectwise tensor product is natural in the two source
modules.** -/
lemma tensorHomOfPairing_precomp
    {q : moduleSheaf (commRingSheaf J O hO) A' ⨯ moduleSheaf (commRingSheaf J O hO) B' ⟶
      moduleSheaf (commRingSheaf J O hO) N}
    (hq : IsBilinearPairing (commRingSheaf J O hO) q) (s : A ⟶ A') (t : B ⟶ B') :
    tensorHomOfPairing (hq.precomp s t) = (_root_.PresheafOfModules.tensorHom s.val t.val) ≫
        tensorHomOfPairing hq := by
  refine PresheafOfModules.hom_ext fun U ↦ ?_
  refine ModuleCat.MonoidalCategory.tensor_ext fun a b ↦ ?_
  exact pairingApp_prodMap_comp q s t U a b

end PresheafTensor

/-! ## The tensor product sheaf over a presheaf of commutative rings -/

section TensorSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {A : Cᵒᵖ ⥤ CommRingCat.{w}} {hA : Presheaf.IsSheaf J
    (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A)}
  {F F' G G' N N' : SheafOfModules.{w} (commRingSheaf J A hA)}

/-- Morphisms of sheaves of modules out of the tensor product sheaf `F ⊗_A G` of Tag 05NA are
the same thing as morphisms of presheaves of modules out of the objectwise tensor product of the
underlying presheaves: the tensor product sheaf is the sheafification of the latter. This is
`Stacks.SheafOfModules.tensorHomEquivPresheafTensorHom` with the sheaf of rings presented as a
presheaf of commutative rings whose underlying presheaf of rings is a sheaf. -/
def tensorSheafHomEquivPresheafTensorHom :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A (forget₂ CommRingCat RingCat) hA⟩).obj F).obj G ⟶
        N) ≃
      (_root_.PresheafOfModules.tensorObj F.val G.val ⟶ N.val) :=
  (PresheafOfModules.sheafificationAdjunction
    (R := commRingSheaf J A hA) (𝟙 _)).homEquiv (_root_.PresheafOfModules.tensorObj F.val G.val) N

/-- **The tensor product sheaf represents bilinear pairings**, for a presheaf of commutative
rings whose underlying presheaf of rings is a sheaf. This is
`Stacks.SheafOfModules.bilinearEquivTensorHom` at the generality in which the inverse image of
a structure sheaf along a morphism of topoi is available: that inverse image is a presheaf of
commutative rings with a sheaf condition on its underlying presheaf of rings, and is never
presented as a sheaf of commutative rings. -/
def bilinearEquivTensorSheafHom :
    { q : moduleSheaf (commRingSheaf J A hA) F ⨯ moduleSheaf (commRingSheaf J A hA) G ⟶
        moduleSheaf (commRingSheaf J A hA) N //
      IsBilinearPairing (commRingSheaf J A hA) q } ≃
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A (forget₂ CommRingCat RingCat) hA⟩).obj F).obj G ⟶
        N) :=
  (bilinearEquivPresheafTensorHom (hO := hA)).trans
    (tensorSheafHomEquivPresheafTensorHom (hA := hA) (F := F) (G := G) (N := N)).symm

omit [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The inverse of `Stacks.SheafOfModules.tensorSheafHomEquivPresheafTensorHom` is natural in
the sheaf of values: this is the right-hand naturality of the sheafification adjunction. -/
lemma tensorSheafHomEquivPresheafTensorHom_symm_naturality
    (t : _root_.PresheafOfModules.tensorObj F.val G.val ⟶ N.val) (k : N ⟶ N') :
    (tensorSheafHomEquivPresheafTensorHom (hA := hA)).symm (t ≫ k.val) =
      (tensorSheafHomEquivPresheafTensorHom (hA := hA) (F := F) (G := G)).symm t ≫ k :=
  (PresheafOfModules.sheafificationAdjunction
    (R := commRingSheaf J A hA) (𝟙 _)).homEquiv_naturality_right_symm t k

omit [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- The inverse of `Stacks.SheafOfModules.tensorSheafHomEquivPresheafTensorHom` is natural in
the two source modules: this is the left-hand naturality of the sheafification adjunction. -/
lemma tensorSheafHomEquivPresheafTensorHom_symm_precomp
    (t : _root_.PresheafOfModules.tensorObj F'.val G'.val ⟶ N.val) (s : F ⟶ F') (u : G ⟶ G') :
    (tensorSheafHomEquivPresheafTensorHom (hA := hA)).symm
        ((_root_.PresheafOfModules.tensorHom s.val u.val) ≫ t) =
      (PresheafOfModules.sheafification (R := commRingSheaf J A hA) (𝟙 _)).map
          (_root_.PresheafOfModules.tensorHom s.val u.val) ≫
        (tensorSheafHomEquivPresheafTensorHom (hA := hA) (F := F') (G := G') (N := N)).symm t :=
  (PresheafOfModules.sheafificationAdjunction
    (R := commRingSheaf J A hA) (𝟙 _)).homEquiv_naturality_left_symm
      (_root_.PresheafOfModules.tensorHom s.val u.val) t

/-- **The universal property of the tensor product sheaf is natural in the sheaf of values.** -/
lemma bilinearEquivTensorSheafHom_naturality
    (q : { q : moduleSheaf (commRingSheaf J A hA) F ⨯ moduleSheaf (commRingSheaf J A hA) G ⟶
        moduleSheaf (commRingSheaf J A hA) N //
      IsBilinearPairing (commRingSheaf J A hA) q }) (k : N ⟶ N') :
    bilinearEquivTensorSheafHom (hA := hA)
        ⟨q.1 ≫ (moduleSheafFunctor (commRingSheaf J A hA)).map k, q.2.comp k⟩ =
      bilinearEquivTensorSheafHom (hA := hA) q ≫ k :=
  (congrArg (fun t ↦ (tensorSheafHomEquivPresheafTensorHom (hA := hA) (F := F) (G := G) (N :=
      N')).symm t)
      (tensorHomOfPairing_comp (hO := hA) q.2 k)).trans
    (tensorSheafHomEquivPresheafTensorHom_symm_naturality (hA := hA) _ k)

/-- **The universal property of the tensor product sheaf is natural in the two source
modules.** -/
lemma bilinearEquivTensorSheafHom_precomp
    (q : { q : moduleSheaf (commRingSheaf J A hA) F' ⨯ moduleSheaf (commRingSheaf J A hA) G' ⟶
        moduleSheaf (commRingSheaf J A hA) N //
      IsBilinearPairing (commRingSheaf J A hA) q }) (s : F ⟶ F') (u : G ⟶ G') :
    bilinearEquivTensorSheafHom (hA := hA)
        ⟨prod.map ((moduleSheafFunctor (commRingSheaf J A hA)).map s)
          ((moduleSheafFunctor (commRingSheaf J A hA)).map u) ≫ q.1, q.2.precomp s u⟩ =
      (PresheafOfModules.sheafification (R := commRingSheaf J A hA) (𝟙 _)).map
          (_root_.PresheafOfModules.tensorHom s.val u.val) ≫
        bilinearEquivTensorSheafHom (hA := hA) q :=
  (congrArg (fun t ↦ (tensorSheafHomEquivPresheafTensorHom (hA := hA) (F := F) (G := G) (N :=
      N)).symm t)
      (tensorHomOfPairing_precomp q.2 s u)).trans
    (tensorSheafHomEquivPresheafTensorHom_symm_precomp (hA := hA) _ s u)

/-- The inverse of `Stacks.SheafOfModules.bilinearEquivTensorSheafHom` is natural in the sheaf of
values: the bilinear pairing of a morphism composed with `k` is the original pairing composed with
`k`. This is the direction the chain of bijections of Tag 03EL traverses. -/
lemma bilinearEquivTensorSheafHom_symm_naturality
    (t : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A (forget₂ CommRingCat RingCat) hA⟩).obj F).obj G ⟶ N)
    (k : N ⟶ N') :
    (bilinearEquivTensorSheafHom (hA := hA) (F := F) (G := G) (N := N')).symm (t ≫ k) =
      ⟨((bilinearEquivTensorSheafHom (hA := hA) (F := F) (G := G) (N := N)).symm t).1 ≫
          (moduleSheafFunctor (commRingSheaf J A hA)).map k,
        ((bilinearEquivTensorSheafHom (hA := hA) (F := F) (G := G) (N := N)).symm t).2.comp k⟩ := by
  refine (bilinearEquivTensorSheafHom (hA := hA) (F := F) (G := G) (N := N')).symm_apply_eq.2 ?_
  simpa using (bilinearEquivTensorSheafHom_naturality (hA := hA)
    ((bilinearEquivTensorSheafHom (hA := hA) (F := F) (G := G) (N := N)).symm t) k).symm

/-- The inverse of `Stacks.SheafOfModules.bilinearEquivTensorSheafHom` is natural in the two
source modules. -/
lemma bilinearEquivTensorSheafHom_symm_precomp
    (t : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨A, Presheaf.isSheaf_of_isSheaf_comp _ A (forget₂ CommRingCat RingCat) hA⟩).obj F').obj G' ⟶
        N)
    (s : F ⟶ F') (u : G ⟶ G') :
    (bilinearEquivTensorSheafHom (hA := hA) (F := F) (G := G) (N := N)).symm
        ((PresheafOfModules.sheafification (R := commRingSheaf J A hA) (𝟙 _)).map
          (_root_.PresheafOfModules.tensorHom s.val u.val) ≫ t) =
      ⟨prod.map ((moduleSheafFunctor (commRingSheaf J A hA)).map s)
            ((moduleSheafFunctor (commRingSheaf J A hA)).map u) ≫
          ((bilinearEquivTensorSheafHom (hA := hA) (F := F') (G := G') (N := N)).symm t).1,
        ((bilinearEquivTensorSheafHom (hA := hA) (F := F') (G := G') (N := N)).symm t).2.precomp s
            u⟩ := by
  refine (bilinearEquivTensorSheafHom (hA := hA) (F := F) (G := G) (N := N)).symm_apply_eq.2 ?_
  have h := bilinearEquivTensorSheafHom_precomp (hA := hA)
    ((bilinearEquivTensorSheafHom (hA := hA) (F := F') (G := G') (N := N)).symm t) s u
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

end TensorSheaf

/-! ## Naturality in the source of the inverse-image bijection -/

section InverseImage

universe w' v' u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
  (O : Sheaf K RingCat.{w'}) {F F' G G' : SheafOfModules.{w'} O}
  (N : SheafOfModules.{w} (inverseImageRingSheaf f O))

/-- The bijection between pairings of the inverse images of two sheaves of modules and pairings
into the direct image is natural in the two source modules. -/
lemma inverseImagePairingEquiv_precomp (u : F ⟶ F') (v : G ⟶ G')
    (q : moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj F') ⨯
        moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj G') ⟶
      moduleSheaf (inverseImageRingSheaf f O) N) :
    inverseImagePairingEquiv f O F G N
        (prod.map ((moduleSheafFunctor (inverseImageRingSheaf f O)).map
            ((inverseImageModules f O).map u))
          ((moduleSheafFunctor (inverseImageRingSheaf f O)).map
            ((inverseImageModules f O).map v)) ≫ q) =
      prod.map ((moduleSheafFunctor O).map u) ((moduleSheafFunctor O).map v) ≫
        inverseImagePairingEquiv f O F' G' N q := by
  have key : prodComparison f.inverseImage (moduleSheaf O F) (moduleSheaf O G) ≫
        (prod.map ((moduleSheafFunctor (inverseImageRingSheaf f O)).map
            ((inverseImageModules f O).map u))
          ((moduleSheafFunctor (inverseImageRingSheaf f O)).map
            ((inverseImageModules f O).map v)) ≫ q) =
      f.inverseImage.map (prod.map ((moduleSheafFunctor O).map u)
          ((moduleSheafFunctor O).map v)) ≫
        (prodComparison f.inverseImage (moduleSheaf O F') (moduleSheaf O G') ≫ q) := by
    rw [moduleSheafFunctor_map_inverseImageModules_map,
      moduleSheafFunctor_map_inverseImageModules_map]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun m ↦ m ≫ q)
          (prodComparison_natural f.inverseImage ((moduleSheafFunctor O).map u)
            ((moduleSheafFunctor O).map v)).symm).trans (Category.assoc _ _ _))
  exact (congrArg (fun m ↦ f.adj.homEquiv (moduleSheaf O F ⨯ moduleSheaf O G)
      (moduleSheaf (inverseImageRingSheaf f O) N) m) key).trans
    (f.adj.homEquiv_naturality_left _ _)

/-- **The bilinear pairings of the inverse images are the bilinear pairings into the direct
image, naturally in the two source modules.** This is the naturality in `F` and `G` of step 3
of the chain of bijections of Tag 03EL. -/
lemma inverseImageBilinearEquiv_precomp (u : F ⟶ F') (v : G ⟶ G')
    (q : { q : moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj F') ⨯
        moduleSheaf (inverseImageRingSheaf f O) ((inverseImageModules f O).obj G') ⟶
          moduleSheaf (inverseImageRingSheaf f O) N //
      IsBilinearPairing (inverseImageRingSheaf f O) q }) :
    (inverseImageBilinearEquiv f O F G N
          ⟨prod.map ((moduleSheafFunctor (inverseImageRingSheaf f O)).map
              ((inverseImageModules f O).map u))
            ((moduleSheafFunctor (inverseImageRingSheaf f O)).map
              ((inverseImageModules f O).map v)) ≫ q.1,
            q.2.precomp _ _⟩).1 =
      prod.map ((moduleSheafFunctor O).map u) ((moduleSheafFunctor O).map v) ≫
        (inverseImageBilinearEquiv f O F' G' N q).1 :=
  inverseImagePairingEquiv_precomp f O N u v q.1

/-- The inverse of `Stacks.SheafOfModules.inverseImageBilinearEquiv` is natural in the sheaf of
values. -/
lemma inverseImageBilinearEquiv_symm_naturality
    {N N' : SheafOfModules.{w} (inverseImageRingSheaf f O)}
    (p : { p : moduleSheaf O F ⨯ moduleSheaf O G ⟶
        moduleSheaf O ((directImageModules f O).obj N) // IsBilinearPairing O p })
    (k : N ⟶ N') :
    (inverseImageBilinearEquiv f O F G N').symm
        ⟨p.1 ≫ (moduleSheafFunctor O).map ((directImageModules f O).map k),
          p.2.comp ((directImageModules f O).map k)⟩ =
      ⟨((inverseImageBilinearEquiv f O F G N).symm p).1 ≫
          (moduleSheafFunctor (inverseImageRingSheaf f O)).map k,
        ((inverseImageBilinearEquiv f O F G N).symm p).2.comp k⟩ := by
  refine (inverseImageBilinearEquiv f O F G N').symm_apply_eq.2 (Subtype.ext ?_)
  simpa using (inverseImageBilinearEquiv_naturality f O F G
    ((inverseImageBilinearEquiv f O F G N).symm p) k).symm

/-- The inverse of `Stacks.SheafOfModules.inverseImageBilinearEquiv` is natural in the two source
modules. -/
lemma inverseImageBilinearEquiv_symm_precomp {N : SheafOfModules.{w} (inverseImageRingSheaf f O)}
    (u : F ⟶ F') (v : G ⟶ G')
    (p : { p : moduleSheaf O F' ⨯ moduleSheaf O G' ⟶
        moduleSheaf O ((directImageModules f O).obj N) // IsBilinearPairing O p }) :
    (inverseImageBilinearEquiv f O F G N).symm
        ⟨prod.map ((moduleSheafFunctor O).map u) ((moduleSheafFunctor O).map v) ≫ p.1,
          p.2.precomp u v⟩ =
      ⟨prod.map ((moduleSheafFunctor (inverseImageRingSheaf f O)).map
              ((inverseImageModules f O).map u))
            ((moduleSheafFunctor (inverseImageRingSheaf f O)).map
              ((inverseImageModules f O).map v)) ≫
          ((inverseImageBilinearEquiv f O F' G' N).symm p).1,
        ((inverseImageBilinearEquiv f O F' G' N).symm p).2.precomp _ _⟩ := by
  refine (inverseImageBilinearEquiv f O F G N).symm_apply_eq.2 (Subtype.ext ?_)
  simpa using (inverseImageBilinearEquiv_precomp f O N u v
    ((inverseImageBilinearEquiv f O F' G' N).symm p)).symm

end InverseImage

end Stacks.SheafOfModules

end
