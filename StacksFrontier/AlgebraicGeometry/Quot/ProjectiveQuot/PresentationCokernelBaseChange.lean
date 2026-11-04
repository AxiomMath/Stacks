module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.PresentationCokernel
public import StacksFrontier.AlgebraicGeometry.Descent.FlatBaseChangeComparison

/-!
# Base change of the twisted family of a Grassmannian presentation

For a Grassmannian presentation `q : 𝒪_T^{⊕ N} ⟶ ℰ` (`N = freeRank n r m`) and `g : T' ⟶ T`, the
inverse image of `ℱ^{(m)}_q = coker(u_m)` along `ℙⁿ_g : ℙⁿ_{T'} ⟶ ℙⁿ_T` is `ℱ^{(m)}_{g^* q}`,
compatibly with the quotient maps out of `𝒪^{⊕ r}(m)`. The inverse image is right exact, so it
carries the cokernel of `u_m` to the cokernel of `(ℙⁿ_g)^* u_m`; the counit identity of the
base-change morphism (`Stacks.Modules.pullback_map_baseChangeNatTrans_app_comp_counit`) and the
base change of the frame `𝒪_T^{⊕ N} ≅ π_*(𝒪^{⊕ r}(m))`
(`AlgebraicGeometry.ProjectiveQuot.pushforwardTwistFreeModuleIso_baseChange`) identify that map
with `u_m` for `g^* ker(q) ⟶ 𝒪_{T'}^{⊕ N}`, which factors through `ker(g^* q)` by an epimorphism
(right exactness of `g^*` again).

## Main definitions

* `AlgebraicGeometry.ProjectiveQuot.frameAdjoint`: the map `π^* M ⟶ 𝒪^{⊕ r}(m)` adjoint to
  `x : M ⟶ 𝒪_T^{⊕ N} ≅ π_*(𝒪^{⊕ r}(m))`; `u_m` is its value at `ker(q) ⟶ 𝒪_T^{⊕ N}`.
* `AlgebraicGeometry.ProjectiveQuot.freeTwistPullbackIso`: `(ℙⁿ_g)^*(𝒪^{⊕ r}(m)) ≅ 𝒪^{⊕ r}(m)`.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.pullbackSquareIso_hom_app_comp_frameAdjoint`: the base
  change of `frameAdjoint`.
* `AlgebraicGeometry.ProjectiveQuot.exists_pullback_presentationCokernel_iso`:
  `(ℙⁿ_g)^* ℱ^{(m)}_q ≅ ℱ^{(m)}_{g^* q}` under `𝒪^{⊕ r}(m)`.
* `AlgebraicGeometry.ProjectiveQuot.exists_presentationCokernel_iso_of_isomorphic`: `ℱ^{(m)}_q`
  only depends on the isomorphism class of `q`.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.AffinePushforward (baseChangeNatTrans)

universe u

namespace AlgebraicGeometry.ProjectiveQuot

variable {n r : ℕ}

/-! ### Two generic facts -/

/-- **Cokernels of maps related by epimorphisms and an isomorphism agree**: if
`p ≫ u ≫ B = p' ≫ u'` with `p`, `p'` epimorphisms and `B` an isomorphism, then
`coker u ≅ coker u'` under `B`. -/
theorem exists_cokernel_iso_of_comp {C : Type*} [Category* C] [Abelian C] {W X X' Y Y' : C}
    (u : X ⟶ Y) (u' : X' ⟶ Y') (p : W ⟶ X) [Epi p] (p' : W ⟶ X') [Epi p'] (B : Y ≅ Y')
    (h : p ≫ u ≫ B.hom = p' ≫ u') :
    ∃ e : cokernel u ≅ cokernel u', cokernel.π u ≫ e.hom = B.hom ≫ cokernel.π u' := by
  have h1 : u ≫ B.hom ≫ cokernel.π u' = 0 :=
    (cancel_epi p).1 (by rw [comp_zero, reassoc_of% h, cokernel.condition, comp_zero])
  have h2 : u' ≫ B.inv ≫ cokernel.π u = 0 :=
    (cancel_epi p').1 (by
      rw [comp_zero, ← Category.assoc p' u', ← h, Category.assoc, Category.assoc,
        Iso.hom_inv_id_assoc, cokernel.condition, comp_zero])
  refine ⟨⟨cokernel.desc u _ h1, cokernel.desc u' _ h2, ?_, ?_⟩, cokernel.π_desc _ _ _⟩
  · refine coequalizer.hom_ext ?_
    rw [cokernel.π_desc_assoc, Category.assoc, cokernel.π_desc, Iso.hom_inv_id_assoc,
      Category.comp_id]
  · refine coequalizer.hom_ext ?_
    rw [cokernel.π_desc_assoc, Category.assoc, cokernel.π_desc, Iso.inv_hom_id_assoc,
      Category.comp_id]

/-- **The counit form of the base-change morphism, transposed.** For a commutative square
`g' ≫ f = f' ≫ g` of schemes, `y : M ⟶ f_* F`, `b : (g')^* F ⟶ F'` and
`z : g^* M ⟶ f'_* F'` with `g^* y ≫ bc_F ≫ f'_* b = z`, the inverse image along `g'` of the
adjoint of `y`, followed by `b`, is the adjoint of `z`. -/
theorem pullbackSquareIso_hom_app_comp_homEquiv_symm {X' X S' S : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S} (w : g' ≫ f = f' ≫ g)
    {M : S.Modules} {F : X.Modules} {F' : X'.Modules}
    (y : M ⟶ (Scheme.Modules.pushforward f).obj F) (b : (Scheme.Modules.pullback g').obj F ⟶ F')
    (z : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pushforward f').obj F')
    (h : (Scheme.Modules.pullback g).map y ≫ (baseChangeNatTrans w).app F ≫
      (Scheme.Modules.pushforward f').map b = z) :
    (Stacks.Modules.pullbackSquareIso f f' g g' w).hom.app M ≫
        (Scheme.Modules.pullback g').map
          (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm y) ≫ b =
      ((Scheme.Modules.pullbackPushforwardAdjunction f').homEquiv _ _).symm z := by
  subst h
  have hn := (Stacks.Modules.pullbackSquareIso f f' g g' w).hom.naturality y
  simp only [Functor.comp_map] at hn
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  calc _ = (Stacks.Modules.pullbackSquareIso f f' g g' w).hom.app M ≫
        (Scheme.Modules.pullback g').map ((Scheme.Modules.pullback f).map y) ≫
        (Scheme.Modules.pullback g').map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F) ≫ b := by
          rw [Functor.map_comp, Category.assoc]
    _ = (Scheme.Modules.pullback f').map ((Scheme.Modules.pullback g).map y) ≫
        (Stacks.Modules.pullbackSquareIso f f' g g' w).hom.app
          ((Scheme.Modules.pushforward f).obj F) ≫
        (Scheme.Modules.pullback g').map
          ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app F) ≫ b := by
          rw [← reassoc_of% hn]
    _ = (Scheme.Modules.pullback f').map ((Scheme.Modules.pullback g).map y) ≫
        (Scheme.Modules.pullback f').map ((baseChangeNatTrans w).app F) ≫
        (Scheme.Modules.pullbackPushforwardAdjunction f').counit.app
          ((Scheme.Modules.pullback g').obj F) ≫ b := by
          rw [← reassoc_of% Stacks.Modules.pullback_map_baseChangeNatTrans_app_comp_counit w F]
    _ = _ := by
          rw [← (Scheme.Modules.pullbackPushforwardAdjunction f').counit_naturality b]
          simp only [Functor.map_comp, Category.assoc]

/-- The canonical map `F(ker q) ⟶ ker(e⁻¹ ≫ F q)` for a functor `F` preserving zero morphisms
and an identification `e : F A ≅ A'`. -/
def kernelLiftMap {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] {A B : C} (q : A ⟶ B) {A' : D} (e : F.obj A ≅ A') :
    F.obj (kernel q) ⟶ kernel (e.inv ≫ F.map q) :=
  kernel.lift _ (F.map (kernel.ι q) ≫ e.hom) (by
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← F.map_comp, kernel.condition, F.map_zero])

/-- `kernelLiftMap F q e` followed by the kernel inclusion is `F (ker q ⟶ A)` followed by
`e`. -/
theorem kernelLiftMap_ι {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] {A B : C} (q : A ⟶ B) {A' : D} (e : F.obj A ≅ A') :
    kernelLiftMap F q e ≫ kernel.ι (e.inv ≫ F.map q) = F.map (kernel.ι q) ≫ e.hom :=
  kernel.lift_ι _ _ _

/-- **Right exactness, read on a kernel**: for an epimorphism `q` and a functor `F` preserving
cokernels, `AlgebraicGeometry.ProjectiveQuot.kernelLiftMap` is an epimorphism. -/
theorem epi_kernelLiftMap {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesColimitsOfShape WalkingParallelPair F]
    {A B : C} (q : A ⟶ B) [Epi q] {A' : D} (e : F.obj A ≅ A') :
    Epi (kernelLiftMap F q e) := by
  have hS := (ShortComplex.kernelSequence_exact q).map_of_epi_of_preservesCokernel F
    (inferInstanceAs (Epi q)) inferInstance
  have h0 : Epi (kernel.lift (F.map q) (F.map (kernel.ι q)) (by
      rw [← F.map_comp, kernel.condition, F.map_zero])) := hS.epi_kernelLift
  let φ : kernel (F.map q) ⟶ kernel (e.inv ≫ F.map q) :=
    kernel.lift _ (kernel.ι (F.map q) ≫ e.hom) (by
      rw [Category.assoc, Iso.hom_inv_id_assoc, kernel.condition])
  let ψ : kernel (e.inv ≫ F.map q) ⟶ kernel (F.map q) :=
    kernel.lift _ (kernel.ι (e.inv ≫ F.map q) ≫ e.inv) (by
      rw [Category.assoc, kernel.condition])
  have hφ : IsIso φ := ⟨⟨ψ, by
      refine equalizer.hom_ext ?_
      rw [Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc, Category.assoc, Iso.hom_inv_id,
        Category.comp_id, Category.id_comp], by
      refine equalizer.hom_ext ?_
      rw [Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc, Category.assoc, Iso.inv_hom_id,
        Category.comp_id, Category.id_comp]⟩⟩
  have heq : kernelLiftMap F q e = kernel.lift (F.map q) (F.map (kernel.ι q)) (by
      rw [← F.map_comp, kernel.condition, F.map_zero]) ≫ φ := by
    refine equalizer.hom_ext ?_
    rw [kernelLiftMap_ι, Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc]
  rw [heq]
  exact @epi_comp _ _ _ _ _ _ h0 _ (@IsIso.epi_of_iso _ _ _ _ _ hφ)

/-- The canonical map `ker f ⟶ ker f'` for `f' = f ≫ e` with `e` an isomorphism. -/
def kernelLiftOfIso {C : Type*} [Category* C] [Abelian C] {A B B' : C}
    (f : A ⟶ B) (f' : A ⟶ B') (e : B ≅ B') (h : f ≫ e.hom = f') : kernel f ⟶ kernel f' :=
  kernel.lift f' (kernel.ι f) (by rw [← h, ← Category.assoc, kernel.condition, zero_comp])

/-- `kernelLiftOfIso` followed by the inclusion of `ker f'` is the inclusion of `ker f`. -/
theorem kernelLiftOfIso_ι {C : Type*} [Category* C] [Abelian C] {A B B' : C}
    (f : A ⟶ B) (f' : A ⟶ B') (e : B ≅ B') (h : f ≫ e.hom = f') :
    kernelLiftOfIso f f' e h ≫ kernel.ι f' = kernel.ι f :=
  kernel.lift_ι _ _ _

/-- An isomorphism of targets identifies the kernels:
`AlgebraicGeometry.ProjectiveQuot.kernelLiftOfIso` is an epimorphism. -/
theorem epi_kernelLiftOfIso {C : Type*} [Category* C] [Abelian C] {A B B' : C}
    (f : A ⟶ B) (f' : A ⟶ B') (e : B ≅ B') (h : f ≫ e.hom = f') :
    Epi (kernelLiftOfIso f f' e h) := by
  let ψ : kernel f' ⟶ kernel f := kernel.lift _ (kernel.ι f') (by
    rw [← cancel_mono e.hom, Category.assoc, h, kernel.condition, zero_comp])
  refine @IsIso.epi_of_iso _ _ _ _ _ ⟨⟨ψ, ?_, ?_⟩⟩
  · refine equalizer.hom_ext ?_
    rw [Category.assoc, kernel.lift_ι, kernelLiftOfIso_ι, Category.id_comp]
  · refine equalizer.hom_ext ?_
    rw [Category.assoc, kernelLiftOfIso_ι, kernel.lift_ι, Category.id_comp]

/-- Bookkeeping in an arbitrary category: `(x ≫ a) ≫ b ≫ c = (x ≫ d) ≫ e` from
`a ≫ b ≫ c = d ≫ e`. -/
theorem comp_comp_comp_eq_of_eq {C : Type*} [Category* C] {A B D E F G : C} (x : A ⟶ B)
    (a : B ⟶ D) (b : D ⟶ E) (c : E ⟶ F) (d : B ⟶ G) (e : G ⟶ F) (h : a ≫ b ≫ c = d ≫ e) :
    (x ≫ a) ≫ b ≫ c = (x ≫ d) ≫ e := by
  rw [Category.assoc, h, Category.assoc]

/-! ### The adjoint of a map into the frame -/

/-- The map `π^* M ⟶ 𝒪^{⊕ r}(m)` on `ℙⁿ_T` adjoint to `x : M ⟶ 𝒪_T^{⊕ N} ≅ π_*(𝒪^{⊕ r}(m))`,
`N = freeRank n r m`. -/
def frameAdjoint (m : ℕ) {T : Scheme.{u}} {M : T.Modules}
    (x : M ⟶ SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin (freeRank.{u} n r m)))) :
    (Scheme.Modules.pullback (projectiveSpaceOver n T ↘ T)).obj M ⟶
      twist (m : ℤ) (freeModule n r T) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (projectiveSpaceOver n T ↘ T)).homEquiv _ _).symm
    (x ≫ (pushforwardTwistFreeModuleIso (n := n) (r := r) T m).inv)

/-- The twisted map of a presentation is the adjoint of the inclusion of its kernel. -/
theorem presentationTwistMap_eq_frameAdjoint (m : ℕ) {T : Scheme.{u}} {k : ℕ}
    (q : Grassmannian.QuotientPresentation T k (freeRank.{u} n r m)) :
    presentationTwistMap m q = frameAdjoint m (kernel.ι q.map) :=
  rfl

/-- `frameAdjoint` is natural in the source: precomposing `x` with `c` precomposes its adjoint
with `π^* c`. -/
theorem frameAdjoint_comp (m : ℕ) {T : Scheme.{u}} {M M' : T.Modules} (c : M' ⟶ M)
    (x : M ⟶ SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin (freeRank.{u} n r m)))) :
    frameAdjoint m (c ≫ x) =
      (Scheme.Modules.pullback (projectiveSpaceOver n T ↘ T)).map c ≫ frameAdjoint m x := by
  unfold frameAdjoint
  exact (congrArg (fun y => ((Scheme.Modules.pullbackPushforwardAdjunction
      (projectiveSpaceOver n T ↘ T)).homEquiv _ _).symm y) (Category.assoc c x _)).trans
    ((Scheme.Modules.pullbackPushforwardAdjunction
      (projectiveSpaceOver n T ↘ T)).homEquiv_naturality_left_symm c _)

variable (n r) in
/-- `(ℙⁿ_g)^*(𝒪^{⊕ r}(m)) ≅ 𝒪^{⊕ r}(m)` on `ℙⁿ_{T'}`. -/
def freeTwistPullbackIso {T' T : Scheme.{u}} (g : T' ⟶ T) (m : ℕ) :
    (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj
        (twist (m : ℤ) (freeModule n r T)) ≅ twist (m : ℤ) (freeModule n r T') :=
  (twistPullbackIso g (m : ℤ) (freeModule n r T)).symm ≪≫
    (twistFunctor n T' (m : ℤ)).mapIso (freeModulePullbackIso n r g)

/-- The forward map of `freeTwistPullbackIso`, written with `twistMap`. -/
theorem freeTwistPullbackIso_hom {T' T : Scheme.{u}} (g : T' ⟶ T) (m : ℕ) :
    (freeTwistPullbackIso n r g m).hom =
      (twistPullbackIso g (m : ℤ) (freeModule n r T)).inv ≫
        twistMap (m : ℤ) (freeModulePullbackIso n r g).hom := by
  rw [twistMap_eq_twistFunctor_map]
  rfl

/-- **Base change of `frameAdjoint`**: along `g : T' ⟶ T`, the inverse image of the adjoint of
`x` is the adjoint of `g^* x` read on `𝒪_{T'}^{⊕ N}`. -/
theorem pullbackSquareIso_hom_app_comp_frameAdjoint (m : ℕ) {T' T : Scheme.{u}} (g : T' ⟶ T)
    {M : T.Modules}
    (x : M ⟶ SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin (freeRank.{u} n r m)))) :
    (Stacks.Modules.pullbackSquareIso _ _ _ _ (isPullback_projectiveSpaceOverMap n g).w).hom.app M ≫
        (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map (frameAdjoint m x) ≫
        (freeTwistPullbackIso n r g m).hom =
      frameAdjoint m ((Scheme.Modules.pullback g).map x ≫
        (Grassmannian.pullbackFreeIso g (freeRank.{u} n r m)).hom) := by
  refine pullbackSquareIso_hom_app_comp_homEquiv_symm _ _ _ _ ?_
  rw [freeTwistPullbackIso_hom]
  exact (congrArg (· ≫ _) ((Scheme.Modules.pullback g).map_comp x _)).trans
    (comp_comp_comp_eq_of_eq (C := T'.Modules) _ _ _ _ _ _
      (pushforwardTwistFreeModuleIso_baseChange n r g m))

/-! ### Base change of `ℱ^{(m)}` -/

/-- The canonical map `g^* ker(q) ⟶ ker(g^* q)` of a Grassmannian presentation; it is an
epimorphism (`AlgebraicGeometry.ProjectiveQuot.epi_kernelPullbackMap`). -/
def kernelPullbackMap {T' T : Scheme.{u}} (g : T' ⟶ T) {k N : ℕ}
    (q : Grassmannian.QuotientPresentation T k N) :
    (Scheme.Modules.pullback g).obj (kernel q.map) ⟶
      kernel (Grassmannian.pullbackPresentation g q).map :=
  kernelLiftMap (Scheme.Modules.pullback g) q.map (Grassmannian.pullbackFreeIso g N)

/-- `kernelPullbackMap g q` followed by the kernel inclusion is `g^*` of the inclusion of
`ker q` followed by `g^* 𝒪^{⊕ N} ≅ 𝒪^{⊕ N}`. -/
theorem kernelPullbackMap_ι {T' T : Scheme.{u}} (g : T' ⟶ T) {k N : ℕ}
    (q : Grassmannian.QuotientPresentation T k N) :
    kernelPullbackMap g q ≫ kernel.ι (Grassmannian.pullbackPresentation g q).map =
      (Scheme.Modules.pullback g).map (kernel.ι q.map) ≫ (Grassmannian.pullbackFreeIso g N).hom :=
  kernelLiftMap_ι _ _ _

/-- `kernelPullbackMap` is an epimorphism, since `g^*` is right exact. -/
instance epi_kernelPullbackMap {T' T : Scheme.{u}} (g : T' ⟶ T) {k N : ℕ}
    (q : Grassmannian.QuotientPresentation T k N) : Epi (kernelPullbackMap g q) := by
  have : PreservesColimitsOfSize.{0, 0} (Scheme.Modules.pullback g) :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).leftAdjoint_preservesColimits
  exact @epi_kernelLiftMap _ _ _ _ _ _ (Scheme.Modules.pullback g) _ _ _ _ q.map q.map_epi _
    (Grassmannian.pullbackFreeIso g N)

/-- The inverse image of modules along a morphism of schemes preserves colimits. -/
private theorem preservesColimitsOfSize_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesColimitsOfSize.{0, 0} (Scheme.Modules.pullback f) :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits

/-- **Base change of `ℱ^{(m)}`**: for `g : T' ⟶ T`, `(ℙⁿ_g)^* ℱ^{(m)}_q ≅ ℱ^{(m)}_{g^* q}`,
compatibly with the quotient maps out of `𝒪^{⊕ r}(m)`. -/
theorem exists_pullback_presentationCokernel_iso (m : ℕ) {T' T : Scheme.{u}} (g : T' ⟶ T)
    {k : ℕ} (q : Grassmannian.QuotientPresentation T k (freeRank.{u} n r m)) :
    ∃ e : (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj (presentationCokernel m q) ≅
        presentationCokernel m (Grassmannian.pullbackPresentation g q),
      (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map (presentationCokernelπ m q) ≫
          e.hom =
        (freeTwistPullbackIso n r g m).hom ≫
          presentationCokernelπ m (Grassmannian.pullbackPresentation g q) := by
  have := preservesColimitsOfSize_pullback (projectiveSpaceOverMap n g)
  have := preservesColimitsOfSize_pullback (projectiveSpaceOver n T' ↘ T')
  let A := (Stacks.Modules.pullbackSquareIso _ _ _ _
    (isPullback_projectiveSpaceOverMap n g).w).app (kernel q.map)
  have hc : Epi ((Scheme.Modules.pullback (projectiveSpaceOver n T' ↘ T')).map
      (kernelPullbackMap g q)) :=
    inferInstance
  have h : A.hom ≫ (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).map
        (presentationTwistMap m q) ≫ (freeTwistPullbackIso n r g m).hom =
      (Scheme.Modules.pullback (projectiveSpaceOver n T' ↘ T')).map (kernelPullbackMap g q) ≫
        presentationTwistMap m (Grassmannian.pullbackPresentation g q) := by
    refine (pullbackSquareIso_hom_app_comp_frameAdjoint m g (kernel.ι q.map)).trans ?_
    rw [← kernelPullbackMap_ι]
    exact frameAdjoint_comp m _ _
  obtain ⟨e₂, he₂⟩ := @exists_cokernel_iso_of_comp _ _ _ _ _ _ _ _ _ _ A.hom
    (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom A)) _ hc (freeTwistPullbackIso n r g m) h
  refine ⟨PreservesCokernel.iso (Scheme.Modules.pullback (projectiveSpaceOverMap n g))
    (presentationTwistMap m q) ≪≫ e₂, ?_⟩
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ e₂.hom) (PreservesCokernel.π_iso_hom
      (Scheme.Modules.pullback (projectiveSpaceOverMap n g)) (presentationTwistMap m q))).trans he₂)

/-- **`ℱ^{(m)}_q` only depends on the isomorphism class of `q`**: isomorphic presentations have
isomorphic twisted families, under `𝒪^{⊕ r}(m)`. -/
theorem exists_presentationCokernel_iso_of_isomorphic (m : ℕ) {T : Scheme.{u}} {k : ℕ}
    {q q' : Grassmannian.QuotientPresentation T k (freeRank.{u} n r m)} (h : q.Isomorphic q') :
    ∃ e : presentationCokernel m q ≅ presentationCokernel m q',
      presentationCokernelπ m q ≫ e.hom = presentationCokernelπ m q' := by
  obtain ⟨eT, heT⟩ := h
  have := preservesColimitsOfSize_pullback (projectiveSpaceOver n T ↘ T)
  have hc := epi_kernelLiftOfIso (C := T.Modules) q.map q'.map eT heT
  have hpc := @Functor.map_epi _ _ _ _ (Scheme.Modules.pullback (projectiveSpaceOver n T ↘ T))
    inferInstance _ _ _ hc
  have h : 𝟙 _ ≫ presentationTwistMap m q ≫ (Iso.refl _).hom =
      (Scheme.Modules.pullback (projectiveSpaceOver n T ↘ T)).map
        (kernelLiftOfIso (C := T.Modules) q.map q'.map eT heT) ≫ presentationTwistMap m q' :=
    (Category.id_comp _).trans ((Category.comp_id _).trans
      ((congrArg (frameAdjoint m)
        (kernelLiftOfIso_ι (C := T.Modules) q.map q'.map eT heT)).symm.trans
        (frameAdjoint_comp m _ _)))
  obtain ⟨e, he⟩ := @exists_cokernel_iso_of_comp _ _ _ _ _ _ _ _ _ _ (𝟙 _) inferInstance _ hpc
    (Iso.refl _) h
  exact ⟨e, he.trans (Category.id_comp _)⟩

end AlgebraicGeometry.ProjectiveQuot

end
