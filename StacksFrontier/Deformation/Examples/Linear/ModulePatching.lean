module

public import StacksFrontier.RingTheory.MilnorPatching.ProjectiveModules
public import StacksFrontier.RingTheory.Localization.Glueing.CategoricalPullback

open ModuleGlueing
/-!
# Reading a module over a ring fibre product as a compatible pair

Let `f : A → C` and `g : B → C` be ring maps with `g` surjective and let `R = A ×_C B` be their
fibre product. Milnor patching identifies flat `R`-modules with pairs of modules over `A` and
over `B` together with an isomorphism of their extensions to `C`. This file packages that
identification in the form the deformation theory of finite projective modules needs: as a
bijection of an `R`-module with the type of compatible pairs, computing the two components as
the prescribed extensions of scalars; and conversely, as the comparison isomorphism determined
by two such extensions and the compatibility of their images over `C`.

The companion statement is that two modules presenting the same compatible pair are isomorphic
over that pair, which is how a module over the fibre product is reconstructed from its two
restrictions.

## Main definitions

* `Deformation.Examples.ringPullbackEquivAlgPullback`: the ring fibre product of two algebra
  maps is the algebra fibre product.
* `Deformation.Examples.semilinearOfBaseChange`: the semilinear map `m ↦ e (1 ⊗ m)` attached to
  an identification of an extension of scalars.

## Main results

* `Deformation.Examples.exists_compatiblePairs_equiv`: a flat module over the fibre product,
  with an identification of its image in the categorical pullback, is in bijection with the
  compatible pairs, computing both components.
* `Deformation.Examples.exists_extensionOfScalarsToPullback_iso`: two identifications of the
  extensions of scalars whose images over `C` agree assemble into an isomorphism in the
  categorical pullback.
* `Deformation.Examples.exists_compatiblePairs_equiv_of_flat`: the first statement for a flat
  module in an arbitrary universe, presented by two linear equivalences.
* `Deformation.Examples.exists_linearEquiv_of_pair_equiv`: two modules presenting the same
  compatible pair are isomorphic compatibly with the two component maps.
* `Deformation.Examples.small_ringHom_pullback`: the fibre product of two small rings is small.
* `Deformation.Examples.subsingleton_of_subsingleton_baseChange`: a finite projective module
  over a local ring is trivial as soon as one nontrivial extension of scalars is.
* `Deformation.Examples.exists_finiteProjectiveModulePatch`: a pair of finite projective
  modules over `A` and `B` with an identification over `C` comes from a finite projective
  module over the fibre product.
* `Deformation.Examples.exists_patch_universal`: the same patch, with its two identifications,
  their compatibility, the injectivity of the induced pair of maps and the universal property
  that makes it the fibre product.

## Implementation notes

The reconstruction statements are existence statements rather than constructions: the
equivalence supplied by Milnor patching is not canonical, only its effect on the two component
maps is, and that is all the use sites need.

## References

* [Stacks Project, Tag 0DVP](https://stacks.math.columbia.edu/tag/0DVP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace Deformation.Examples

universe u v t w

/-- A flat module over the fibre product of `f` and `g`, together with an identification `i` of
its image in the categorical pullback, is in bijection with the compatible pairs for `f` and
`g`, and the bijection computes both components of the pair as the images under `i` of the two
extensions of scalars. -/
public theorem exists_compatiblePairs_equiv
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* C) (g : B →+* C) (s : RingFibreProduct.Situation f g (RingHom.ker g))
    (N : ModuleCat.{u} s.fibreProduct) [Module.Flat s.fibreProduct N]
    (X : CategoricalPullback (ModuleCat.extendScalars.{u, u, u} f)
      (ModuleCat.extendScalars.{u, u, u} g))
    (i : (ModuleGlueing.extensionOfScalarsToPullback s.pullbackCone.fst.hom
      s.pullbackCone.snd.hom f g
      (congrArg CommRingCat.Hom.hom s.pullbackCone.condition)).obj N ≅ X) :
    ∃ e : N ≃ MilnorPatching.CompatiblePairs f g X, ∀ n : N,
      (e n).1.1 = i.hom.fst ((1 : A) ⊗ₜ[s.fibreProduct, s.pullbackCone.fst.hom] n) ∧
      (e n).1.2 = i.hom.snd ((1 : B) ⊗ₜ[s.fibreProduct, s.pullbackCone.snd.hom] n) := by
  obtain ⟨F, e, adj, he, hc, hf, hu, hq⟩ :=
    MilnorPatching.flatModulesEquivalenceOverFibreProduct f g (RingHom.ker g) s
  let := hu N inferInstance
  let j : N ≅ F.obj X := asIso (adj.unit.app N) ≪≫ F.mapIso i
  refine ⟨j.toLinearEquiv.toEquiv.trans (e X), fun n => ?_⟩
  have hh := he N X (adj.homEquiv N X i.hom) n
  have hj : adj.homEquiv N X i.hom = j.hom := adj.homEquiv_unit N X i.hom
  have hsym : (adj.homEquiv N X).symm (adj.homEquiv N X i.hom) = i.hom :=
    (adj.homEquiv N X).symm_apply_apply i.hom
  rwa [hsym, hj] at hh

private lemma tensor_cast_one
    {R S : Type u} [CommRing R] [CommRing S]
    (f g : R →+* S) (h : f = g) (N : ModuleCat.{u} R) (n : N) :
    ((eqToIso (congrArg ModuleCat.extendScalars h)).hom.app N)
      ((1 : S) ⊗ₜ[R, f] n) = (1 : S) ⊗ₜ[R, g] n := by
  cases h
  rfl

/-- Two identifications of the extensions of scalars of `N` along `p` and `q` whose images in
`C` agree assemble into an isomorphism in the categorical pullback, with the prescribed
components. -/
public theorem exists_extensionOfScalarsToPullback_iso
    {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    (p : R →+* A) (q : R →+* B) (f : A →+* C) (g : B →+* C)
    (h : f.comp p = g.comp q) (N : ModuleCat.{u} R)
    (X : CategoricalPullback (ModuleCat.extendScalars.{u, u, u} f)
      (ModuleCat.extendScalars.{u, u, u} g))
    (a : (ModuleCat.extendScalars p).obj N ≅ X.fst)
    (b : (ModuleCat.extendScalars q).obj N ≅ X.snd)
    (hab : ∀ n : N, X.iso.hom ((1 : C) ⊗ₜ[A, f] a.hom ((1 : A) ⊗ₜ[R, p] n)) =
      (1 : C) ⊗ₜ[B, g] b.hom ((1 : B) ⊗ₜ[R, q] n)) :
    ∃ i : (ModuleGlueing.extensionOfScalarsToPullback p q f g h).obj N ≅ X,
      i.hom.fst = a.hom ∧ i.hom.snd = b.hom := by
  refine ⟨CategoricalPullback.mkIso a b ?_, rfl, rfl⟩
  apply (cancel_epi ((ModuleGlueing.extendScalarsComp p f).hom.app N)).mp
  apply ModuleCat.ExtendScalars.hom_ext
  intro n
  change X.iso.hom ((ModuleCat.extendScalars f).map a.hom
      ((ModuleGlueing.extendScalarsComp p f).hom.app N
        ((1 : C) ⊗ₜ[R, f.comp p] n))) = _
  rw [ModuleGlueing.extendScalarsComp_hom_app_one_tmul]
  change X.iso.hom ((1 : C) ⊗ₜ[A, f] (a.hom ((1 : A) ⊗ₜ[R, p] n))) = _
  rw [hab]
  change _ = (ModuleCat.extendScalars g).map b.hom
    (((ModuleGlueing.extendScalarsComp p f).symm ≪≫
      eqToIso (congrArg ModuleCat.extendScalars h) ≪≫
      ModuleGlueing.extendScalarsComp q g).hom.app N
      ((ModuleGlueing.extendScalarsComp p f).hom.app N ((1 : C) ⊗ₜ[R, f.comp p] n)))
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, ConcreteCategory.comp_apply]
  have hi : (ModuleGlueing.extendScalarsComp p f).inv.app N
      ((ModuleGlueing.extendScalarsComp p f).hom.app N ((1 : C) ⊗ₜ[R, f.comp p] n)) =
      (1 : C) ⊗ₜ[R, f.comp p] n :=
    ((ModuleGlueing.extendScalarsComp p f).app N).toLinearEquiv.symm_apply_apply _
  rw [hi]
  have hcast := tensor_cast_one (f.comp p) (g.comp q) h N n
  have hone := ModuleGlueing.extendScalarsComp_hom_app_one_tmul q g N n
  have hchain := (congrArg
    (fun z => ((ModuleGlueing.extendScalarsComp q g).hom.app N) z) hcast).trans hone
  exact (congrArg (fun z => ((ModuleCat.extendScalars g).map b.hom) z) hchain).symm

/-- The reconstruction statement of `exists_compatiblePairs_equiv` for a flat module whose
carrier lies in an arbitrary universe, presented by two linear equivalences from its extensions
of scalars. -/
public theorem exists_compatiblePairs_equiv_of_flat
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* C) (g : B →+* C) (s : RingFibreProduct.Situation f g (RingHom.ker g))
    (N : Type v) [AddCommGroup N] [Module s.fibreProduct N]
    [Small.{u} N] [Module.Flat s.fibreProduct N]
    (X : CategoricalPullback (ModuleCat.extendScalars.{u, u, u} f)
      (ModuleCat.extendScalars.{u, u, u} g))
    (a : letI : Algebra s.fibreProduct A := s.pullbackCone.fst.hom.toAlgebra
      TensorProduct s.fibreProduct A N ≃ₗ[A] X.fst)
    (b : letI : Algebra s.fibreProduct B := s.pullbackCone.snd.hom.toAlgebra
      TensorProduct s.fibreProduct B N ≃ₗ[B] X.snd)
    (hab : ∀ n : N, X.iso.hom ((1 : C) ⊗ₜ[A, f]
        a ((1 : A) ⊗ₜ[s.fibreProduct, s.pullbackCone.fst.hom] n)) =
      (1 : C) ⊗ₜ[B, g] b ((1 : B) ⊗ₜ[s.fibreProduct, s.pullbackCone.snd.hom] n)) :
    ∃ e : N ≃ MilnorPatching.CompatiblePairs f g X, ∀ n : N,
      (e n).1.1 = a ((1 : A) ⊗ₜ[s.fibreProduct, s.pullbackCone.fst.hom] n) ∧
      (e n).1.2 = b ((1 : B) ⊗ₜ[s.fibreProduct, s.pullbackCone.snd.hom] n) := by
  let : Algebra s.fibreProduct A := s.pullbackCone.fst.hom.toAlgebra
  let : Algebra s.fibreProduct B := s.pullbackCone.snd.hom.toAlgebra
  let N' := Shrink.{u} N
  let en : N' ≃ₗ[s.fibreProduct] N := Shrink.linearEquiv s.fibreProduct N
  let a' := (LinearEquiv.baseChange s.fibreProduct A _ _ en).trans a
  let b' := (LinearEquiv.baseChange s.fibreProduct B _ _ en).trans b
  obtain ⟨i, hi₁, hi₂⟩ := exists_extensionOfScalarsToPullback_iso s.pullbackCone.fst.hom
    s.pullbackCone.snd.hom f g (congrArg CommRingCat.Hom.hom s.pullbackCone.condition)
    (ModuleCat.of s.fibreProduct N') X a'.toModuleIso b'.toModuleIso (fun n => hab (en n))
  obtain ⟨e, he⟩ := exists_compatiblePairs_equiv f g s (ModuleCat.of s.fibreProduct N') X i
  refine ⟨en.symm.toEquiv.trans e, fun n => ?_⟩
  have hh := he (en.symm n)
  rw [hi₁, hi₂] at hh
  change (e (en.symm n)).1.1 =
      a ((1 : A) ⊗ₜ[s.fibreProduct, s.pullbackCone.fst.hom] en (en.symm n)) ∧
    (e (en.symm n)).1.2 =
      b ((1 : B) ⊗ₜ[s.fibreProduct, s.pullbackCone.snd.hom] en (en.symm n)) at hh
  rw [en.apply_symm_apply] at hh
  exact hh

/-- Two modules presenting the same pairs of images under a fixed pair of semilinear maps are
isomorphic, compatibly with those maps. -/
public theorem exists_linearEquiv_of_pair_equiv
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : R →+* B)
    {M N M₁ M₂ : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup M₁] [AddCommGroup M₂] [Module R M] [Module R N]
    [Module A M₁] [Module B M₂]
    (a₁ : M →ₛₗ[f] M₁) (a₂ : M →ₛₗ[g] M₂)
    (b₁ : N →ₛₗ[f] M₁) (b₂ : N →ₛₗ[g] M₂)
    (S : M₁ × M₂ → Prop)
    (eM : M ≃ {x // S x}) (eN : N ≃ {x // S x})
    (hM : ∀ m, (eM m).1 = (a₁ m, a₂ m))
    (hN : ∀ n, (eN n).1 = (b₁ n, b₂ n)) :
    ∃ e : M ≃ₗ[R] N, ∀ m, b₁ (e m) = a₁ m ∧ b₂ (e m) = a₂ m := by
  let e := eM.trans eN.symm
  have he (m : M) : b₁ (e m) = a₁ m ∧ b₂ (e m) = a₂ m :=
    Prod.mk.inj (by rw [← hN, ← hM]; simp [e])
  have hinj {x y : N} (h₁ : b₁ x = b₁ y) (h₂ : b₂ x = b₂ y) : x = y := by
    apply eN.injective
    apply Subtype.ext
    rw [hN, hN, h₁, h₂]
  refine ⟨{ e with map_add' := ?_, map_smul' := ?_ }, he⟩
  · intro x y
    apply hinj
    · change b₁ (e (x + y)) = b₁ (e x + e y)
      rw [map_add b₁, (he _).1, (he _).1, (he _).1, map_add]
    · change b₂ (e (x + y)) = b₂ (e x + e y)
      rw [map_add b₂, (he _).2, (he _).2, (he _).2, map_add]
  · intro r x
    apply hinj
    · change b₁ (e (r • x)) = b₁ (r • e x)
      rw [map_smulₛₗ b₁, (he _).1, (he _).1, map_smulₛₗ]
    · change b₂ (e (r • x)) = b₂ (r • e x)
      rw [map_smulₛₗ b₂, (he _).2, (he _).2, map_smulₛₗ]

/-- The fibre product of two small rings is small. -/
public theorem small_ringHom_pullback
    {A B C : Type w} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* C) (g : B →+* C) [Small.{t, w} A] [Small.{t, w} B] :
    Small.{t, w} (RingHom.pullback f g) :=
  small_of_injective (f := fun x : RingHom.pullback f g => x.1) Subtype.val_injective

/-- A finite projective module over a local ring is trivial as soon as one of its extensions of
scalars along a map to a nontrivial ring is. -/
public theorem subsingleton_of_subsingleton_baseChange
    {R S M : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [Nontrivial S] [Algebra R S]
    (h : Subsingleton (TensorProduct R S M)) : Subsingleton M := by
  classical
  have : Module.Free R M := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis R M
  have : Finite (Module.Free.ChooseBasisIndex R M) := Module.Finite.finite_basis b
  by_contra hM
  have : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
  obtain ⟨i⟩ := b.index_nonempty
  let b' := b.baseChange S
  simpa using congrArg (fun m => b'.repr m i) (h.elim (b' i) 0)

/-- The fibre product of two algebra maps, as a ring, is the fibre product as an algebra. -/
public noncomputable def ringPullbackEquivAlgPullback
    {Λ : Type u} {A₁ A₂ A : Type w}
    [CommRing Λ] [CommRing A₁] [CommRing A₂] [CommRing A]
    [Algebra Λ A₁] [Algebra Λ A₂] [Algebra Λ A]
    (f₁ : A₁ →ₐ[Λ] A) (f₂ : A₂ →ₐ[Λ] A) :
    RingHom.pullback f₁.toRingHom f₂.toRingHom ≃+* AlgHom.pullback f₁ f₂ where
  toFun x := ⟨x.1, by change f₁ x.1.1 = f₂ x.1.2; exact x.2⟩
  invFun x := ⟨x.1, by change f₁.toRingHom x.1.1 = f₂.toRingHom x.1.2; exact x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- The semilinear map `m ↦ e (1 ⊗ m)` attached to an identification `e` of an extension of
scalars. -/
public noncomputable def semilinearOfBaseChange
    {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (f : R →+* S)
    (e : letI : Algebra R S := f.toAlgebra; TensorProduct R S M ≃ₗ[S] N) :
    M →ₛₗ[f] N := by
  letI : Algebra R S := f.toAlgebra
  refine { toFun := fun m => e (TensorProduct.tmul R (1 : S) m)
           map_add' := fun m n => by rw [TensorProduct.tmul_add, map_add]
           map_smul' := ?_ }
  intro r m
  rw [TensorProduct.tmul_smul]
  change e ((f r) • TensorProduct.tmul R (1 : S) m) = _
  exact e.map_smul _ _

/-- A pair of finite projective modules over `R₁` and `R₂` together with an identification of
their extensions of scalars to `R` comes from a finite projective module over the fibre
product, under the equivalence of Milnor patching. -/
public theorem exists_finiteProjectiveModulePatch
    {R₁ R₂ R : Type w} [CommRing R₁] [CommRing R₂] [CommRing R]
    (f₁ : R₁ →+* R) (f₂ : R₂ →+* R) (hf₂ : Function.Surjective f₂)
    (M₁ : Type t) [AddCommGroup M₁] [Module R₁ M₁] [Small.{w, t} M₁]
      [Module.Finite R₁ M₁] [Module.Projective R₁ M₁]
    (M₂ : Type t) [AddCommGroup M₂] [Module R₂ M₂] [Small.{w, t} M₂]
      [Module.Finite R₂ M₂] [Module.Projective R₂ M₂]
    (e : letI : Algebra R₁ R := f₁.toAlgebra
      letI : Algebra R₂ R := f₂.toAlgebra
      TensorProduct R₁ R M₁ ≃ₗ[R] TensorProduct R₂ R M₂) :
    letI : Algebra R₁ R := f₁.toAlgebra
    letI : Algebra R₂ R := f₂.toAlgebra
    let e' := (LinearEquiv.baseChange R₁ R (Shrink.{w, t} M₁) M₁
        (Shrink.linearEquiv R₁ M₁)).trans
      (e.trans (LinearEquiv.baseChange R₂ R (Shrink.{w, t} M₂) M₂
        (Shrink.linearEquiv R₂ M₂)).symm)
    let s : RingFibreProduct.Situation f₁ f₂ (RingHom.ker f₂) := ⟨hf₂, rfl⟩
    let E := ModuleGlueing.extensionOfScalarsToPullback s.pullbackCone.fst.hom
      s.pullbackCone.snd.hom f₁ f₂ (congrArg CommRingCat.Hom.hom s.pullbackCone.condition)
    let X := CategoricalPullback.mk (ModuleCat.of R₁ (Shrink.{w, t} M₁))
      (ModuleCat.of R₂ (Shrink.{w, t} M₂)) e'.toModuleIso
    ∃ N : ModuleCat.{w} s.fibreProduct,
      Module.Finite s.fibreProduct N ∧ Module.Projective s.fibreProduct N ∧
      Nonempty (E.obj N ≅ X) := by
  classical
  let : Algebra R₁ R := f₁.toAlgebra
  let : Algebra R₂ R := f₂.toAlgebra
  let M₁' := Shrink.{w, t} M₁
  let M₂' := Shrink.{w, t} M₂
  let e₁ : M₁' ≃ₗ[R₁] M₁ := Shrink.linearEquiv R₁ M₁
  let e₂ : M₂' ≃ₗ[R₂] M₂ := Shrink.linearEquiv R₂ M₂
  let e' := (LinearEquiv.baseChange R₁ R M₁' M₁ e₁).trans
    (e.trans (LinearEquiv.baseChange R₂ R M₂' M₂ e₂).symm)
  let I : Ideal R₂ := RingHom.ker f₂
  let s : RingFibreProduct.Situation f₁ f₂ I := ⟨hf₂, rfl⟩
  let E := ModuleGlueing.extensionOfScalarsToPullback s.pullbackCone.fst.hom
    s.pullbackCone.snd.hom f₁ f₂ (congrArg CommRingCat.Hom.hom s.pullbackCone.condition)
  let P : ObjectProperty (ModuleCat.{w} s.fibreProduct) :=
    fun N ↦ Module.Finite s.fibreProduct N ∧ Module.Projective s.fibreProduct N
  let Q : ObjectProperty
      (CategoricalPullback (ModuleCat.extendScalars.{w, w, w} f₁)
        (ModuleCat.extendScalars.{w, w, w} f₂)) :=
      fun X ↦ (Module.Finite R₁ X.fst ∧ Module.Projective R₁ X.fst) ∧
        (Module.Finite R₂ X.snd ∧ Module.Projective R₂ X.snd)
  let X : Q.FullSubcategory :=
    ⟨CategoricalPullback.mk (ModuleCat.of R₁ M₁') (ModuleCat.of R₂ M₂') e'.toModuleIso,
      by constructor <;> constructor <;> infer_instance⟩
  obtain ⟨q, hq⟩ :=
    MilnorPatching.finiteProjectiveModulesEquivalenceOverFibreProduct f₁ f₂ I s
  let N₀ : P.FullSubcategory := q.inverse.obj X
  let hqiso : P.ι ⋙ E ≅ q.functor ⋙ Q.ι := Classical.choice hq
  exact ⟨N₀.obj, N₀.property.1, N₀.property.2,
    ⟨hqiso.app N₀ ≪≫ Q.ι.mapIso (q.counitIso.app X)⟩⟩

/-- Milnor patching for finite projective modules, in the form a deformation problem uses it.
Given finite projective modules `M₁` over `R₁` and `M₂` over `R₂` and an identification `e` of
their extensions of scalars to `R`, with `R₂ → R` surjective, there is a finite projective
module `N` over the ring fibre product `R₁ ×_R R₂`, together with identifications `ε₁, ε₂` of
its two extensions of scalars with `M₁` and `M₂`, such that

* the two identifications agree over `R` through `e`;
* the pair of induced maps `n ↦ (ε₁ (1 ⊗ n), ε₂ (1 ⊗ n))` is injective;
* every flat module over the fibre product carrying the same two identifications is isomorphic
  to `N` compatibly with them.

These three statements are what the Rim–Schlessinger condition for finite projective modules
needs of the patch: the first makes the patch a cone, the second makes the cone jointly monic,
and the third makes every competing cone factor through it. -/
public theorem exists_patch_universal
    {R₁ R₂ R : Type w} [CommRing R₁] [CommRing R₂] [CommRing R]
    (f₁ : R₁ →+* R) (f₂ : R₂ →+* R) (hf₂ : Function.Surjective f₂)
    (M₁ : Type t) [AddCommGroup M₁] [Module R₁ M₁] [Small.{w, t} M₁]
      [Module.Finite R₁ M₁] [Module.Projective R₁ M₁]
    (M₂ : Type t) [AddCommGroup M₂] [Module R₂ M₂] [Small.{w, t} M₂]
      [Module.Finite R₂ M₂] [Module.Projective R₂ M₂]
    (e : letI : Algebra R₁ R := f₁.toAlgebra
      letI : Algebra R₂ R := f₂.toAlgebra
      TensorProduct R₁ R M₁ ≃ₗ[R] TensorProduct R₂ R M₂) :
    letI : Algebra R₁ R := f₁.toAlgebra
    letI : Algebra R₂ R := f₂.toAlgebra
    let s : RingFibreProduct.Situation f₁ f₂ (RingHom.ker f₂) := ⟨hf₂, rfl⟩
    letI : Algebra s.fibreProduct R₁ := s.pullbackCone.fst.hom.toAlgebra
    letI : Algebra s.fibreProduct R₂ := s.pullbackCone.snd.hom.toAlgebra
    ∃ (N : ModuleCat.{w} s.fibreProduct),
      Module.Finite s.fibreProduct N ∧ Module.Projective s.fibreProduct N ∧
      ∃ (ε₁ : TensorProduct s.fibreProduct R₁ N ≃ₗ[R₁] M₁)
        (ε₂ : TensorProduct s.fibreProduct R₂ N ≃ₗ[R₂] M₂),
        (∀ n : N, e (TensorProduct.tmul R₁ (1 : R)
              (ε₁ (TensorProduct.tmul s.fibreProduct (1 : R₁) n))) =
            TensorProduct.tmul R₂ (1 : R)
              (ε₂ (TensorProduct.tmul s.fibreProduct (1 : R₂) n))) ∧
        Function.Injective (fun n : N =>
            (ε₁ (TensorProduct.tmul s.fibreProduct (1 : R₁) n),
              ε₂ (TensorProduct.tmul s.fibreProduct (1 : R₂) n))) ∧
        ∀ (M : Type t) [AddCommGroup M] [Module s.fibreProduct M] [Small.{w, t} M]
          [Module.Flat s.fibreProduct M]
          (a₁ : TensorProduct s.fibreProduct R₁ M ≃ₗ[R₁] M₁)
          (a₂ : TensorProduct s.fibreProduct R₂ M ≃ₗ[R₂] M₂),
          (∀ m : M, e (TensorProduct.tmul R₁ (1 : R)
                (a₁ (TensorProduct.tmul s.fibreProduct (1 : R₁) m))) =
              TensorProduct.tmul R₂ (1 : R)
                (a₂ (TensorProduct.tmul s.fibreProduct (1 : R₂) m))) →
          ∃ l : M ≃ₗ[s.fibreProduct] N,
            ∀ m : M,
              ε₁ (TensorProduct.tmul s.fibreProduct (1 : R₁) (l m)) =
                  a₁ (TensorProduct.tmul s.fibreProduct (1 : R₁) m) ∧
                ε₂ (TensorProduct.tmul s.fibreProduct (1 : R₂) (l m)) =
                  a₂ (TensorProduct.tmul s.fibreProduct (1 : R₂) m) := by
  classical
  let : Algebra R₁ R := f₁.toAlgebra
  let : Algebra R₂ R := f₂.toAlgebra
  let s : RingFibreProduct.Situation f₁ f₂ (RingHom.ker f₂) := ⟨hf₂, rfl⟩
  let toR₁ : s.fibreProduct →+* R₁ := s.pullbackCone.fst.hom
  let toR₂ : s.fibreProduct →+* R₂ := s.pullbackCone.snd.hom
  let : Algebra s.fibreProduct R₁ := toR₁.toAlgebra
  let : Algebra s.fibreProduct R₂ := toR₂.toAlgebra
  let sh₁ : Shrink.{w, t} M₁ ≃ₗ[R₁] M₁ := Shrink.linearEquiv R₁ M₁
  let sh₂ : Shrink.{w, t} M₂ ≃ₗ[R₂] M₂ := Shrink.linearEquiv R₂ M₂
  let e' := (LinearEquiv.baseChange R₁ R (Shrink.{w, t} M₁) M₁ sh₁).trans
    (e.trans (LinearEquiv.baseChange R₂ R (Shrink.{w, t} M₂) M₂ sh₂).symm)
  let X : CategoricalPullback (ModuleCat.extendScalars.{w, w, w} f₁)
      (ModuleCat.extendScalars.{w, w, w} f₂) :=
    CategoricalPullback.mk (ModuleCat.of R₁ (Shrink.{w, t} M₁))
      (ModuleCat.of R₂ (Shrink.{w, t} M₂)) e'.toModuleIso
  obtain ⟨N, hNfin, hNproj, hNiso⟩ :=
    exists_finiteProjectiveModulePatch f₁ f₂ hf₂ M₁ M₂ e
  have : Module.Finite s.fibreProduct N := hNfin
  have : Module.Projective s.fibreProduct N := hNproj
  have : Module.Flat s.fibreProduct N := Module.Flat.of_projective
  let patchIso : (ModuleGlueing.extensionOfScalarsToPullback s.pullbackCone.fst.hom
      s.pullbackCone.snd.hom f₁ f₂
      (congrArg CommRingCat.Hom.hom s.pullbackCone.condition)).obj N ≅ X :=
    Classical.choice hNiso
  let ep₁ : TensorProduct s.fibreProduct R₁ N ≃ₗ[R₁] Shrink.{w, t} M₁ :=
    ((CategoricalPullback.π₁ _ _).mapIso patchIso).toLinearEquiv
  let ep₂ : TensorProduct s.fibreProduct R₂ N ≃ₗ[R₂] Shrink.{w, t} M₂ :=
    ((CategoricalPullback.π₂ _ _).mapIso patchIso).toLinearEquiv
  let ε₁ : TensorProduct s.fibreProduct R₁ N ≃ₗ[R₁] M₁ := ep₁.trans sh₁
  let ε₂ : TensorProduct s.fibreProduct R₂ N ≃ₗ[R₂] M₂ := ep₂.trans sh₂
  obtain ⟨pairs, hpairs⟩ := exists_compatiblePairs_equiv f₁ f₂ s N X patchIso
  have hep₁ (n : N) : (pairs n).1.1 = ep₁ (TensorProduct.tmul s.fibreProduct (1 : R₁) n) :=
    (hpairs n).1
  have hep₂ (n : N) : (pairs n).1.2 = ep₂ (TensorProduct.tmul s.fibreProduct (1 : R₂) n) :=
    (hpairs n).2
  have hpair (n : N) :
      X.iso.hom ((1 : R) ⊗ₜ[R₁, f₁] ep₁ ((1 : R₁) ⊗ₜ[s.fibreProduct, toR₁] n)) =
        (1 : R) ⊗ₜ[R₂, f₂] ep₂ ((1 : R₂) ⊗ₜ[s.fibreProduct, toR₂] n) := by
    have hh := (pairs n).property
    rwa [hep₁ n, hep₂ n] at hh
  have key (x₁ : Shrink.{w, t} M₁) (x₂ : Shrink.{w, t} M₂) :
      e' (TensorProduct.tmul R₁ (1 : R) x₁) = TensorProduct.tmul R₂ (1 : R) x₂ ↔
        e (TensorProduct.tmul R₁ (1 : R) (sh₁ x₁)) = TensorProduct.tmul R₂ (1 : R) (sh₂ x₂) := by
    simp only [e', LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq, LinearEquiv.baseChange_tmul]
  have hcompat (n : N) :
      e (TensorProduct.tmul R₁ (1 : R)
          (ε₁ (TensorProduct.tmul s.fibreProduct (1 : R₁) n))) =
        TensorProduct.tmul R₂ (1 : R)
          (ε₂ (TensorProduct.tmul s.fibreProduct (1 : R₂) n)) :=
    (key _ _).1 (hpair n)
  refine ⟨N, hNfin, hNproj, ε₁, ε₂, hcompat, ?_, ?_⟩
  · intro n n' hn
    refine pairs.injective (Subtype.ext (Prod.ext ?_ ?_))
    · rw [hep₁ n, hep₁ n']
      exact sh₁.injective (congrArg Prod.fst hn)
    · rw [hep₂ n, hep₂ n']
      exact sh₂.injective (congrArg Prod.snd hn)
  · intro M _ _ _ _ a₁ a₂ hcomp
    let ashr := a₁.trans sh₁.symm
    let bshr := a₂.trans sh₂.symm
    obtain ⟨eM, heM⟩ := exists_compatiblePairs_equiv_of_flat f₁ f₂ s M X ashr bshr (by
      intro m
      refine (key _ _).2 ?_
      erw [sh₁.apply_symm_apply, sh₂.apply_symm_apply]
      exact hcomp m)
    obtain ⟨eN, heN⟩ := exists_compatiblePairs_equiv_of_flat f₁ f₂ s N X ep₁ ep₂ hpair
    obtain ⟨l, hl⟩ := exists_linearEquiv_of_pair_equiv toR₁ toR₂
      (semilinearOfBaseChange toR₁ ashr)
      (semilinearOfBaseChange toR₂ bshr)
      (semilinearOfBaseChange toR₁ ep₁)
      (semilinearOfBaseChange toR₂ ep₂) _ eM eN
      (fun m => Prod.ext (heM m).1 (heM m).2)
      (fun n => Prod.ext (heN n).1 (heN n).2)
    refine ⟨l, fun m => ?_⟩
    have hl₁ : ep₁ (TensorProduct.tmul s.fibreProduct (1 : R₁) (l m)) =
        sh₁.symm (a₁ (TensorProduct.tmul s.fibreProduct (1 : R₁) m)) := (hl m).1
    have hl₂ : ep₂ (TensorProduct.tmul s.fibreProduct (1 : R₂) (l m)) =
        sh₂.symm (a₂ (TensorProduct.tmul s.fibreProduct (1 : R₂) m)) := (hl m).2
    refine ⟨?_, ?_⟩
    · change sh₁ (ep₁ (TensorProduct.tmul s.fibreProduct (1 : R₁) (l m))) = _
      rw [hl₁, LinearEquiv.apply_symm_apply]
    · change sh₂ (ep₂ (TensorProduct.tmul s.fibreProduct (1 : R₂) (l m))) = _
      rw [hl₂, LinearEquiv.apply_symm_apply]

end Deformation.Examples
