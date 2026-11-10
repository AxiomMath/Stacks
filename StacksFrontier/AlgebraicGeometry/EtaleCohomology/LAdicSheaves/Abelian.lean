module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Normality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Presentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The category of `ℤ_ℓ`-sheaves on a Noetherian scheme is abelian

Everything turns on one statement: **every epimorphism of ℓ-adic sheaves admits a kernel whose
levelwise kernel comparisons are epimorphisms**. The kernel is built from the quotient
presentation of the tower of levelwise kernels: the presenting ℓ-adic sheaf maps to the source,
pro-monomorphically, which makes the map a monomorphism and a kernel, and the presentation's
surjectivity makes each levelwise comparison an epimorphism.

That single statement discharges the three things still missing. It gives normality of
epimorphisms directly, through the criterion of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Normality`. Applied to the
projection onto the levelwise cokernel it gives the image factorisation of an arbitrary
morphism, whose epimorphism half is exactly where the presentation's levelwise surjectivity is
used again. Kernels in general then follow by composing the kernel of the epimorphic part with
the monomorphic part, and normality of monomorphisms follows because a morphism which is both a
monomorphism and an epimorphism in the factorisation is an isomorphism.

With the preadditive structure, the finite biproducts and the levelwise cokernels already in
place, the two normality halves complete Mathlib's definition of an abelian category.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.normalized_epi_kernel_exists`: the pivot.
* `Stacks.EtaleCohomology.LAdicSheaf.hasKernels`: the category has kernels.
* `Stacks.EtaleCohomology.LAdicSheaf.abelian`: **Stacks 03UO**, the category of ℓ-adic sheaves
  on a Noetherian scheme is abelian.

## References

* [Stacks Project, Tag 03UO](https://stacks.math.columbia.edu/tag/03UO)
* [Stacks Project, Tag 03UM](https://stacks.math.columbia.edu/tag/03UM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [Fact ℓ.Prime] [IsNoetherian X.1]

attribute [local instance] underlyingLevelFunctor_additive
  underlyingLevelFunctor_preservesMonomorphisms underlyingLevelFunctor_isLeftAdjoint
  underlyingLevelFunctor_preservesKernels underlyingLevelFunctor_full

namespace LAdicSheaf

attribute [local instance] underlyingLAdicLevel_noetherian underlyingTransitionLE_epi
  underlyingRawKernelι_mono underlyingLAdicFunctor_additive underlyingLAdicFunctor_full
  underlyingLAdicFunctor_faithful

/-- The factorisation of a morphism through its abelian image is an epimorphism. Mathlib has
this as an instance, but resolving it at the finite levels of an ℓ-adic sheaf exhausts the
instance-search budget; stated abstractly it is immediate, and applying it costs nothing. -/
public theorem epi_factorThruImage {C : Type*} [Category C] [Abelian C] {A D : C} (g : A ⟶ D) :
    Epi (Abelian.factorThruImage g) := inferInstance

/-- Passing to the underlying tower, read on morphisms. The functor's action is the induced map
of towers; naming it keeps every composition below spelled with `underlyingLAdicTower`, which
is what lets the associativity rewrites find their pattern. -/
public theorem underlyingLAdicFunctor_map {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) :
    (underlyingLAdicFunctor B X ℓ).map f = underlyingLAdicTowerMap B X ℓ f := rfl

/-- A map killed by `g` is killed by whatever kills `kernel.ι g`. -/
private theorem comp_eq_zero_of_kernel_ι_comp_eq_zero {C : Type*} [Category C]
    [Limits.HasZeroMorphisms C] {A Y Z W : C} {g : Y ⟶ Z} [HasKernel g] {x : A ⟶ Y}
    (hx : x ≫ g = 0) {t : Y ⟶ W} (ht : kernel.ι g ≫ t = 0) : x ≫ t = 0 := by
  rw [← kernel.lift_ι _ _ hx, Category.assoc, ht, comp_zero]

/-- **The pivot of Stacks 03UO.** Every epimorphism of ℓ-adic sheaves admits a kernel whose
levelwise kernel comparisons are epimorphisms, and which moreover dies, level by level, under a
high enough transition map of its own underlying tower.

The kernel is the ℓ-adic sheaf presenting the tower of levelwise kernels. It maps to the source
through the presentation, and that map is pro-monomorphic, which is what makes it a
monomorphism and a kernel; the presentation's surjectivity at each level makes the levelwise
comparisons epimorphisms. -/
public theorem normalized_epi_kernel_exists {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G)
    [Epi f] :
    ∃ K : LAdicSheaf.{u, u + 1} B X ℓ, ∃ i : K ⟶ F, ∃ w : i ≫ f = 0,
      Nonempty (IsLimit (KernelFork.ofι i w)) ∧
      (∀ n, Epi (kernel.lift (f.app n) (i.app n) (comp_eq_zero_app i f w n))) ∧
      (∀ n, ∃ m : ℕ, ∃ h : n ≤ m,
        kernel.ι ((underlyingLevelFunctor B X ℓ m).map (i.app m)) ≫
          underlyingTransitionLE B X ℓ K h = 0) := by
  classical
  obtain ⟨H, ⟨P, hP⟩⟩ := epiKernel_has_presentation B X ℓ f
  let K := sheafOfPresentation B X ℓ H P hP
  let e := sheafOfPresentationIso B X ℓ H P hP
  let U := underlyingLAdicFunctor B X ℓ
  let j := presentationMap P (underlyingLAdicTower B X ℓ F)
    (underlyingRawKernelInclusion B X ℓ f) (underlyingLAdicLevel_annihilated B X ℓ F)
  let i : K ⟶ F := U.preimage (e.hom ≫ j)
  have hi : U.map i = e.hom ≫ j := U.map_preimage _
  have hi' : underlyingLAdicTowerMap B X ℓ i = e.hom ≫ j := hi
  -- The components of the comparison isomorphism and of the presentation map, written at the
  -- spelling in which the levels of the underlying towers are declared. Without this the
  -- compositions below mix two definitionally equal descriptions of one object and no rewrite
  -- can find its pattern.
  let eh : ∀ n : ℕ, underlyingLAdicLevel B X ℓ K n ⟶ P.obj n :=
    fun n => e.hom.app (Opposite.op n)
  let ei : ∀ n : ℕ, P.obj n ⟶ underlyingLAdicLevel B X ℓ K n :=
    fun n => e.inv.app (Opposite.op n)
  let jn : ∀ n : ℕ, P.obj n ⟶ underlyingLAdicLevel B X ℓ F n :=
    fun n => j.app (Opposite.op n)
  have hiapp : ∀ m : ℕ, (underlyingLevelFunctor B X ℓ m).map (i.app m) = eh m ≫ jn m :=
    fun m => NatTrans.congr_app hi' (Opposite.op m)
  have heieh : ∀ n : ℕ, ei n ≫ eh n = 𝟙 (P.obj n) := fun n => e.inv_hom_id_app _
  have hehei : ∀ n : ℕ, eh n ≫ ei n = 𝟙 (underlyingLAdicLevel B X ℓ K n) :=
    fun n => e.hom_inv_id_app _
  have hehIso : ∀ n : ℕ, IsIso (eh n) := fun n => ⟨⟨ei n, hehei n, heieh n⟩⟩
  have hjf : j ≫ underlyingLAdicTowerMap B X ℓ f = 0 :=
    presentationMap_comp_eq_zero P _ _ _ _ _ (underlyingRawKernelInclusion_condition B X ℓ f)
  have w : i ≫ f = 0 := by
    apply U.map_injective
    have h : underlyingLAdicTowerMap B X ℓ i ≫ underlyingLAdicTowerMap B X ℓ f = 0 := by
      rw [hi', Category.assoc, hjf, comp_zero]
    rw [U.map_comp, U.map_zero]
    exact h
  have hp : ∀ n, ∃ m : ℕ, ∃ h : n ≤ m,
      kernel.ι ((underlyingLevelFunctor B X ℓ m).map (i.app m)) ≫
        underlyingTransitionLE B X ℓ K h = 0 := by
    intro n
    refine ⟨P.index n, P.le_index n, ?_⟩
    set m := P.index n
    set x := kernel.ι ((underlyingLevelFunctor B X ℓ m).map (i.app m))
    have hx : (x ≫ eh m) ≫ jn m = 0 := by
      rw [Category.assoc, ← hiapp m]
      exact kernel.condition _
    have hz : kernel.ι (jn m) ≫ towerMap (presentationTower P) (P.le_index n) = 0 :=
      presentationMap_pro_mono P (underlyingLAdicTower B X ℓ F)
        (underlyingRawKernelInclusion B X ℓ f) (underlyingLAdicLevel_annihilated B X ℓ F)
        (underlyingRawKernelι_mono B X ℓ f) (n := n) (m := m) (le_refl _)
    have hnat : underlyingTransitionLE B X ℓ K (P.le_index n) ≫ eh n =
        eh m ≫ towerMap (presentationTower P) (P.le_index n) :=
      e.hom.naturality (homOfLE (P.le_index n)).op
    have := hehIso n
    refine (cancel_mono (eh n)).1 ?_
    rw [Category.assoc, hnat, ← Category.assoc, zero_comp]
    exact comp_eq_zero_of_kernel_ι_comp_eq_zero hx hz
  have : Mono i := Preadditive.mono_of_cancel_zero i (fun {A} a ha => by
    apply U.map_injective
    rw [U.map_zero]
    refine towerHom_eq_zero_of_pro_mono (underlyingLAdicTowerMap B X ℓ i)
      (fun n m h => underlyingTransitionLE_epi B X ℓ A h) hp
      (underlyingLAdicTowerMap B X ℓ a) ?_
    have hac : underlyingLAdicTowerMap B X ℓ a ≫ underlyingLAdicTowerMap B X ℓ i =
        underlyingLAdicTowerMap B X ℓ (a ≫ i) := (U.map_comp a i).symm
    rw [hac, ha]
    exact U.map_zero _ _)
  have hlim : IsLimit (KernelFork.ofι i w) := by
    apply KernelFork.IsLimit.ofι'
    intro A a ha
    let l := presentationLift P (underlyingLAdicTower B X ℓ A)
      (underlyingRawKernelLift B X ℓ f a ha) (underlyingLAdicLevel_annihilated B X ℓ A)
      (fun n m h => underlyingTransitionLE_isCokernel B X ℓ A h)
    have hcomp : (l ≫ e.inv) ≫ (e.hom ≫ j) = l ≫ j := by
      rw [Category.assoc, ← Category.assoc e.inv, e.inv_hom_id, Category.id_comp]
    refine ⟨U.preimage (l ≫ e.inv), U.map_injective ?_⟩
    rw [U.map_comp, U.map_preimage, hi]
    exact hcomp.trans ((presentationLift_map P _ _ _ _ _ _ _).trans
      (underlyingRawKernelLift_fac B X ℓ f a ha))
  refine ⟨K, i, w, ⟨hlim⟩, ?_, hp⟩
  intro n
  set b := kernel.lift (f.app n) (i.app n) (comp_eq_zero_app i f w n) with hbdef
  have hbj : (underlyingLevelFunctor B X ℓ n).map b ≫ underlyingRawKernelι B X ℓ f n =
      eh n ≫ jn n := by
    rw [underlyingRawKernelι, ← Functor.map_comp, hbdef, kernel.lift_ι, hiapp n]
  let tk : underlyingRawKernelLevel B X ℓ f (P.index n) ⟶
      underlyingRawKernelLevel B X ℓ f n :=
    towerMap (underlyingRawKernelTower B X ℓ f) (P.le_index n)
  have hfacι : (underlyingRawKernelInclusion B X ℓ f).app (Opposite.op (P.index n)) ≫
      towerMap (underlyingLAdicTower B X ℓ F) (P.le_index n) =
        tk ≫ underlyingRawKernelι B X ℓ f n :=
    ((underlyingRawKernelInclusion B X ℓ f).naturality (homOfLE (P.le_index n)).op).symm
  have hπj : P.π n ≫ jn n = tk ≫ underlyingRawKernelι B X ℓ f n :=
    (presentationMap_fac P _ _ _ n).trans hfacι
  have hb : (P.π n ≫ ei n) ≫ (underlyingLevelFunctor B X ℓ n).map b = tk := by
    refine (cancel_mono (underlyingRawKernelι B X ℓ f n)).1 ?_
    rw [Category.assoc, hbj, ← Category.assoc, Category.assoc (P.π n), heieh n,
      Category.comp_id]
    exact hπj
  have : Epi ((P.π n ≫ ei n) ≫ (underlyingLevelFunctor B X ℓ n).map b) := by
    rw [hb]
    exact underlyingRawKernelTower_epi B X ℓ f (P.le_index n)
  have : Epi ((underlyingLevelFunctor B X ℓ n).map b) := epi_of_epi (P.π n ≫ ei n) _
  exact (underlyingLevelFunctor B X ℓ n).epi_of_epi_map (f := b) inferInstance

/-- **Stacks 03UO**, normality of epimorphisms: every epimorphism of ℓ-adic sheaves is a
cokernel. -/
@[stacks 03UO "every epimorphism is a cokernel"]
public instance normalEpiCategory : IsNormalEpiCategory (LAdicSheaf.{u, u + 1} B X ℓ) where
  normalEpiOfEpi f _ := by
    obtain ⟨K, i, w, _, hc, _⟩ := normalized_epi_kernel_exists B X ℓ f
    exact ⟨normalEpi_of_epi_kernelLift i f w hc⟩

/-- Every morphism of ℓ-adic sheaves factors as an epimorphism followed by a monomorphism which
is a kernel. The epimorphism half is where the levelwise surjectivity of the presentation is
used: the kernel comparison of the factorisation is an epimorphism and dies under a high enough
transition map, so the factorisation itself is an epimorphism at every level. -/
public theorem image_factorization {F G : LAdicSheaf.{u, u + 1} B X ℓ} (f : F ⟶ G) :
    ∃ E : LAdicSheaf.{u, u + 1} B X ℓ, ∃ a : F ⟶ E, ∃ i : E ⟶ G,
      Epi a ∧ Mono i ∧ a ≫ i = f ∧ Nonempty (NormalMono i) := by
  let p := cokernelSystemπ f
  have : Epi p := (epi_iff_app_epi p).2 (fun n => by
    change Epi (cokernel.π (f.app n))
    infer_instance)
  obtain ⟨E, i, w, ⟨hi⟩, hb, hp⟩ := normalized_epi_kernel_exists B X ℓ p
  let a := (KernelFork.IsLimit.lift' hi f (comp_cokernelSystemπ f)).1
  have ha : a ≫ i = f := (KernelFork.IsLimit.lift' hi f _).2
  have : Mono i := Fork.IsLimit.mono hi
  have haepi : Epi a := by
    apply (epi_iff_app_epi a).2
    intro n
    obtain ⟨m, hnm, hm⟩ := hp n
    let V := underlyingLevelFunctor B X ℓ m
    let b := kernel.lift (p.app m) (i.app m) (comp_eq_zero_app i p w m)
    let t := underlyingTransitionLE B X ℓ E hnm
    have : Epi b := hb m
    have hab : a.app m ≫ b = Abelian.factorThruImage (f.app m) := by
      refine (cancel_mono (kernel.ι (p.app m))).1 ?_
      calc (a.app m ≫ b) ≫ kernel.ι (p.app m)
          = a.app m ≫ (b ≫ kernel.ι (p.app m)) := Category.assoc _ _ _
        _ = a.app m ≫ i.app m := by rw [kernel.lift_ι]
        _ = f.app m := congrArg (fun z : F ⟶ G => z.app m) ha
        _ = Abelian.factorThruImage (f.app m) ≫ kernel.ι (p.app m) :=
            (Abelian.image.fac (f.app m)).symm
    have : Epi (V.map (a.app m) ≫ V.map b) := by
      have := epi_factorThruImage (f.app m)
      have h1 : Epi (V.map (Abelian.factorThruImage (f.app m))) :=
        (underlyingLevelFunctor B X ℓ m).map_epi _
      rw [← V.map_comp, hab]
      exact h1
    have hk : kernel.ι (V.map b) ≫ t = 0 := by
      have hkb : kernel.ι (V.map b) ≫ V.map (i.app m) = 0 := by
        have he : V.map b ≫ V.map (kernel.ι (p.app m)) = V.map (i.app m) := by
          rw [← V.map_comp, kernel.lift_ι]
        rw [← he, ← Category.assoc, kernel.condition, zero_comp]
      exact comp_eq_zero_of_kernel_ι_comp_eq_zero hkb hm
    have : Epi t := underlyingTransitionLE_epi B X ℓ E hnm
    have : Epi (V.map (a.app m) ≫ t) :=
      epi_comp_of_kernel_annihilated (V.map (a.app m)) (V.map b) t hk
    have hn : underlyingTransitionLE B X ℓ F hnm ≫
        (underlyingLevelFunctor B X ℓ n).map (a.app n) = V.map (a.app m) ≫ t := by
      have hnat := (underlyingLAdicTowerMap B X ℓ a).naturality (homOfLE hnm).op
      rw [underlyingLAdicTowerMap_app, underlyingLAdicTowerMap_app] at hnat
      exact hnat
    have : Epi ((underlyingLevelFunctor B X ℓ n).map (a.app n)) := epi_of_epi_fac hn
    exact (underlyingLevelFunctor B X ℓ n).epi_of_epi_map (f := a.app n) inferInstance
  exact ⟨E, a, i, haepi, inferInstance, ha, ⟨{ Z := _, g := p, w := w, isLimit := hi }⟩⟩

/-- **Stacks 03UO**, the kernel part: the category of ℓ-adic sheaves on a Noetherian scheme has
kernels. The kernel of a morphism is the kernel of the epimorphism in its image
factorisation. -/
@[stacks 03UO "kernels"]
public instance hasKernels : HasKernels (LAdicSheaf.{u, u + 1} B X ℓ) := by
  refine ⟨fun {F G} f => ?_⟩
  obtain ⟨E, a, i, ha, hi, hfac, _⟩ := image_factorization B X ℓ f
  have := ha
  have := hi
  obtain ⟨K, j, w, ⟨hj⟩, _, _⟩ := normalized_epi_kernel_exists B X ℓ a
  exact HasLimit.mk ⟨_, isKernelCompMono hj i hfac.symm⟩

/-- **Stacks 03UO**, normality of monomorphisms: every monomorphism of ℓ-adic sheaves is a
kernel. In the image factorisation of a monomorphism the epimorphic half is also a
monomorphism, hence an isomorphism, so the monomorphism is the kernel the factorisation
provides. -/
@[stacks 03UO "every monomorphism is a kernel"]
public instance normalMonoCategory : IsNormalMonoCategory (LAdicSheaf.{u, u + 1} B X ℓ) where
  normalMonoOfMono f _ := by
    obtain ⟨E, a, i, ha, hi, hfac, ⟨hn⟩⟩ := image_factorization B X ℓ f
    have := ha
    have : Mono a := mono_of_mono_fac hfac
    have : StrongEpi a := strongEpi_of_epi a
    have : IsIso a := isIso_of_mono_of_strongEpi a
    refine ⟨{ Z := hn.Z, g := hn.g, w := ?_, isLimit := ?_ }⟩
    · rw [← hfac, Category.assoc, hn.w, comp_zero]
    · exact IsLimit.ofIsoLimit hn.isLimit (Fork.ext (asIso a).symm (by
        change inv a ≫ f = i
        rw [← hfac, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]))

/-- **Stacks 03UO.** The category of `ℤ_ℓ`-sheaves on a Noetherian scheme is abelian: it is
preadditive with finite biproducts, has kernels and cokernels, and every monomorphism is a
kernel while every epimorphism is a cokernel. -/
@[stacks 03UO,
  sga "5 V 3.2" "abelian",
  sga "4½ Rapport 2.6" "abelian",
  sga "5 VI 1.1.3" "special case"]
public instance abelian : Abelian (LAdicSheaf.{u, u + 1} B X ℓ) where
  normalMonoOfMono f _ := (normalMonoCategory B X ℓ).normalMonoOfMono f
  normalEpiOfEpi f _ := (normalEpiCategory B X ℓ).normalEpiOfEpi f

end LAdicSheaf

end Stacks.EtaleCohomology

end
