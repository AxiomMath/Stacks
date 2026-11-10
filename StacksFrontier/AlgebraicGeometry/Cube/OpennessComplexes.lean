module

public import StacksFrontier.AlgebraicGeometry.Cube.OpennessSetup
public import StacksFrontier.AlgebraicGeometry.Cube.SeesawClosed
public import StacksFrontier.AlgebraicGeometry.Size.Pullback
public import StacksFrontier.AlgebraicGeometry.Perfect.CohomologyAndBaseChangeVanishing

/-!
# Finiteness of the Čech complexes of the openness step of the cube

In the notation of `StacksFrontier/AlgebraicGeometry/Cube/OpennessSetup.lean`: for finite affine
covers `UX` of `X` and `UY` of `Y`, schemes proper over a field `k`, a Noetherian `k`-algebra `R`
and an invertible module `L` on `Q = (X ×_k Y) ×_k Spec R`, the product family `W` is a finite
affine cover of `Q` with affine finite intersections, and the three alternating Čech complexes
`C`, `DX`, `DY` of `L` and of its two face restrictions are bounded complexes of flat `R`-modules
whose images in `D(R)` are perfect ([Stacks, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)).

These are the finiteness inputs of the module-theoretic heart of the openness step,
[Stacks, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2).

## Main results

* `AlgebraicGeometry.Cube.Openness.isAffineOpen_W`, `iSup_W`, `isAffineOpen_iInf_W`.
* `AlgebraicGeometry.Cube.Openness.isPerfect_C`, `isPerfect_DX`, `isPerfect_DY`.
* `AlgebraicGeometry.Cube.Openness.flat_C`, `flat_DX`, `flat_DY`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

noncomputable section

namespace AlgebraicGeometry.Cube.Openness

attribute [local instance 10000] HasDerivedCategory.standard

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (x : Spec (.of k) ⟶ X) (hx : x ≫ f = 𝟙 _) (y : Spec (.of k) ⟶ Y) (hy : y ≫ g = 𝟙 _)
  (R : Type u) [CommRing R] [Algebra k R]
  {I J : Type u} (UX : I → X.Opens) (UY : J → Y.Opens)

/-- The members of the product family are affine. -/
theorem isAffineOpen_W (hUX : ∀ a, IsAffineOpen (UX a)) (hUY : ∀ b, IsAffineOpen (UY b))
    (s : I × J) : IsAffineOpen (W f g R UX UY s) := by
  have : IsAffine (UX s.1).toScheme := hUX s.1
  have : IsAffine (UY s.2).toScheme := hUY s.2
  have : IsAffine (⊤ : (Spec (.of k)).Opens).toScheme := isAffineOpen_top (Spec (.of k))
  have : IsAffineHom (φR (k := k) R) := isAffineHom_of_isAffine _
  have : IsAffineHom (pullback.fst (pullback.fst f g ≫ f) (φR R)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (pullback.fst f g ≫ f) (φR R)).flip inferInstance
  exact (isAffineOpen_inf_preimage f g (U := UX s.1) (V := UY s.2)
    (S₀ := (⊤ : (Spec (.of k)).Opens)) (by simp) (by simp)).preimage _

/-- The product family covers `Q`. -/
theorem iSup_W (hUX : (⊤ : X.Opens) = ⨆ a, UX a) (hUY : (⊤ : Y.Opens) = ⨆ b, UY b) :
    (⊤ : (Q f g R).Opens) = ⨆ s, W f g R UX UY s := by
  refine (eq_top_iff.2 fun z _ => ?_).symm
  let z' := pullback.fst (pullback.fst f g ≫ f) (φR R) z
  have ha : pullback.fst f g z' ∈ (⨆ a, UX a) := hUX ▸ trivial
  have hb : pullback.snd f g z' ∈ (⨆ b, UY b) := hUY ▸ trivial
  obtain ⟨a, ha⟩ := Opens.mem_iSup.1 ha
  obtain ⟨b, hb⟩ := Opens.mem_iSup.1 hb
  exact Opens.mem_iSup.2 ⟨(a, b), ⟨ha, hb⟩⟩

variable [IsProper f] [IsProper g]

/-- The finite intersections of members of the product family are affine. -/
theorem isAffineOpen_iInf_W (hUX : ∀ a, IsAffineOpen (UX a)) (hUY : ∀ b, IsAffineOpen (UY b))
    (r : ℕ) (s : Fin (r + 1) → I × J) : IsAffineOpen (⨅ k, W f g R UX UY (s k)) :=
  Stacks.Cech.inter_isAffineOpen (qR f g R) (W f g R UX UY) (isAffineOpen_W f g R UX UY hUX hUY) s

/-- The face `jX : X_R ⟶ Q` is an affine morphism. -/
instance : IsAffineHom (jX f g y hy R) := by
  let p : Q f g R ⟶ XR f R := pullback.map _ _ _ _ (pullback.fst f g) (𝟙 _) (𝟙 _)
    (by simp) (by simp)
  have hp : jX f g y hy R ≫ p = 𝟙 _ := by
    apply pullback.hom_ext
    · simp only [jX, p, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Category.id_comp]
      simp
    · simp only [jX, p, Category.assoc, pullback.lift_snd,
        Category.comp_id, Category.id_comp]
  have : IsSeparated (p ≫ qX f R) := by
    rw [show p ≫ qX f R = qR f g R by simp only [p, qX, qR, pullback.lift_snd, Category.comp_id]]
    infer_instance
  have : IsSeparated p := IsSeparated.of_comp p (qX f R)
  have : IsAffineHom (jX f g y hy R ≫ p) := by
    rw [hp]
    infer_instance
  exact IsAffineHom.of_comp (jX f g y hy R) p

/-- The face `jY : Y_R ⟶ Q` is an affine morphism. -/
instance : IsAffineHom (jY f g x hx R) := by
  let p : Q f g R ⟶ YR g R := pullback.map _ _ _ _ (pullback.snd f g) (𝟙 _) (𝟙 _)
    (by simp [pullback.condition]) (by simp)
  have hp : jY f g x hx R ≫ p = 𝟙 _ := by
    apply pullback.hom_ext
    · simp only [jY, p, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        pullback.lift_snd, Category.comp_id, Category.id_comp]
    · simp only [jY, p, Category.assoc, pullback.lift_snd,
        Category.comp_id, Category.id_comp]
  have : IsSeparated (p ≫ qY g R) := by
    rw [show p ≫ qY g R = qR f g R by simp only [p, qY, qR, pullback.lift_snd, Category.comp_id]]
    infer_instance
  have : IsSeparated p := IsSeparated.of_comp p (qY g R)
  have : IsAffineHom (jY f g x hx R ≫ p) := by
    rw [hp]
    infer_instance
  exact IsAffineHom.of_comp (jY f g x hx R) p

section Generic

open Stacks.AlgebraicGeometry.ProperFlatGlobalSections

variable {A : Type u} [CommRing A] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of A)) {K : Type u}
  (V : K → Z.Opens) (L : Z.Modules)

/-- **The alternating Čech complex of a coherent module flat over a Noetherian base, on a finite
affine cover with affine finite intersections of a scheme proper over the base, has perfect
image in `D(A)`** ([Stacks, Tag 07VK]): it is the Čech model of `RΓ(Z, L)`. -/
theorem isPerfect_extend_alternatingCechModuleComplex [IsNoetherianRing A] [IsProper h]
    [Finite K] [LinearOrder K] (hV : (⊤ : Z.Opens) = ⨆ i, V i) (hVa : ∀ i, IsAffineOpen (V i))
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → K), IsAffineOpen (⨅ k, V (s k))) [L.IsCoherent]
    (hflat : IsFlatOver h.toLRSHom.toShHom L) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj
      ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} A)).obj
        (Stacks.Cech.alternatingCechModuleComplex h V L))) := by
  have : Fintype K := Fintype.ofFinite K
  have : L.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent L).1
  exact StacksDraft.Perfect.isPerfect_of_iso
    (DerivedCategory.Q.mapIso (baseAlternatingCechComplexIsoExtend h V hV L)).symm
    (isPerfect_Q_baseAlternatingCechComplex h V hV L hVa haff hflat)

/-- An invertible module on a scheme flat and locally of finite type over a Noetherian ring is
coherent and flat over the base. -/
theorem coherent_flat_of_isInvertible [IsNoetherianRing A] [Flat h] [LocallyOfFiniteType h]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.property L) :
    L.IsCoherent ∧ IsFlatOver h.toLRSHom.toShHom L := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian h
  have : L.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible Z L
  have : L.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent L).1
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (R := Z.ringCatSheaf) L 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme Z L
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := Z.ringCatSheaf) L :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  exact ⟨inferInstance,
    AlgebraicGeometry.VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree h L⟩

end Generic

end AlgebraicGeometry.Cube.Openness

end

end
