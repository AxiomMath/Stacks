module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCharacterization.Assembly
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCanonical.RepresentativeUniqueness
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.ShiftedHomTransport
public import StacksFrontier.AlgebraicGeometry.Duality.InternalHom.LocallySmall
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PullbackPushforwardDerivedTensor
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# The characterization of the complex of [Stacks, Tag 0DJU], [Stacks, Tag 0DJV]

For the complex `L = hocolim (Rf_*R𝓗om(Kₙ, E))^∨` of [Stacks, Tag 0DJU] this file proves:

* `nonempty_naturalHomIdentification`: a natural identification
  `Hom(L, N) ≃ Hom(K, E ⊗^L Lf^*N)` for `N` in `D^+_{QCoh}(𝒪_S)`;
* `extEquiv`, `extEquiv_naturality`, `extEquiv_comp_singleδ`: the resulting identifications
  `Ext^i_{𝒪_S}(L, ℱ) ≃ Ext^i_{𝒪_X}(K, E ⊗^L Lf^*ℱ)` for `ℱ` quasi-coherent, natural in `ℱ` and
  compatible with the boundary maps of short exact sequences;
* `exists_iso_of_naturalHomIdentification`: an object with quasi-coherent cohomology carrying
  such a natural identification is isomorphic to `L`, compatibly with the identifications.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Triangulated
open Opposite MonoidalCategory AlgebraicGeometry

universe u

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

namespace Stacks.AlgebraicGeometry.RelativeExtCharacterization

open Stacks.SheafOfModules Stacks.AlgebraicGeometry.RelativeDerivedHomDual
open Stacks.Cohomology.RelativeExtCanonical

attribute [local instance] derivedMonoidalStructure derivedSymmetricStructure

/-- `D^+_{QCoh}(𝒪_S)`, the bounded below objects with quasi-coherent cohomology, at the standard
model. -/
abbrev boundedBelowQCoh (S : Scheme.{u}) : ObjectProperty (DStd S) :=
  boundedBelowQuasicoherent S

/-- The `i`-th cohomology sheaf on `D(𝒪_Z)` at the standard model. -/
abbrev hStd (Z : Scheme.{u}) (i : ℤ) : DStd Z ⥤ Z.Modules :=
  @DerivedCategory.homologyFunctor Z.Modules _ _ (HasDerivedCategory.standard _) i

variable {X S : Scheme.{u}} (f : X ⟶ S) (E : DStd X)

/-- `R𝓗om(P, E)` has quasi-coherent cohomology for `P` perfect and `E` in `D_QCoh`
([Stacks, Tag 0A6H]). -/
theorem isQuasicoherent_rhom (P : DStd X) (hP : IsPerfectSite P)
    (hE : ∀ i : ℤ, ((hStd X i).obj E).IsQuasicoherent)
    (i : ℤ) :
    ((hStd X i).obj (rhom P E)).IsQuasicoherent :=
  Stacks.Duality.InternalHom.derivedCategoryB_derivedSheafHom_of_isPerfect X P E
    (isPerfect_ringedSpace_of_isPerfectSite hP) hE i

/-- The projection formula map at `(R𝓗om(P, E), N)` is invertible for `N` in `D_QCoh`
([Stacks, Tag 08EU]). -/
theorem isIso_pfMap [QuasiCompact f] [QuasiSeparated f] (P : DStd X) (hP : IsPerfectSite P)
    (hE : ∀ i : ℤ, ((hStd X i).obj E).IsQuasicoherent)
    (N : DStd S)
    (hN : ∀ i : ℤ, ((hStd S i).obj N).IsQuasicoherent) :
    IsIso (pfMap f (rhom P E) N) :=
  Stacks.Cohomology.ProjectionFormulaQCoh.isIso_projectionFormulaMap_of_isDQCoh f (rhom P E) N
    (isQuasicoherent_rhom E P hP hE) hN

/-- The derived tensor product of [Stacks, Tag 06YU] on `D(𝒪_Z)`, at the standard model. -/
abbrev canonicalTensor (Z : Scheme.{u}) :
    @Stacks.SheafOfModules.DerivedTensorProduct (ringedSite Z.sheaf) _ _
      (HasDerivedCategory.standard _) _ _ _ :=
  @Stacks.SheafOfModules.canonicalDerivedTensorProduct (ringedSite Z.sheaf) _ _ _ _ _
    (HasDerivedCategory.standard _)

/-- `E ⊗^L -` commutes with the shift: the one-variable half of the two-variable commutation of
the derived tensor product of [Stacks, Tag 06YU]. -/
instance instCommShiftTensorObj (E : DStd X) : ((derivedTensor X.sheaf).obj E).CommShift ℤ :=
  @Stacks.SheafOfModules.DerivedTensorProduct.commShift_right (ringedSite X.sheaf) _ _
    (HasDerivedCategory.standard _) _ _ _ (canonicalTensor X) E

/-- `E ⊗^L -` is a triangulated functor. -/
instance instIsTriangulatedTensorObj (E : DStd X) :
    ((derivedTensor X.sheaf).obj E).IsTriangulated :=
  @Stacks.SheafOfModules.DerivedTensorProduct.exact_right (ringedSite X.sheaf) _ _
    (HasDerivedCategory.standard _) _ _ _ (canonicalTensor X) E

/-- The functor placing a module in degree zero, at the standard model. -/
abbrev singleStd (Z : Scheme.{u}) : Z.Modules ⥤ DStd Z :=
  @DerivedCategory.singleFunctor Z.Modules _ _ (HasDerivedCategory.standard _) 0

/-- The connecting morphism `ℱ₃ ⟶ ℱ₁[1]` of a short exact sequence of `𝒪_Z`-modules, at the
standard model. -/
abbrev singleδStd {Z : Scheme.{u}} {T : ShortComplex Z.Modules} (hT : T.ShortExact) :
    (singleStd Z).obj T.X₃ ⟶ ((singleStd Z).obj T.X₁)⟦(1 : ℤ)⟧ :=
  @ShortComplex.ShortExact.singleδ _ _ _ (HasDerivedCategory.standard _) T hT

/-- The distinguished triangle `ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ ℱ₁[1]` of a short exact sequence of
`𝒪_Z`-modules, at the standard model. -/
abbrev singleTriangleStd {Z : Scheme.{u}} {T : ShortComplex Z.Modules} (hT : T.ShortExact) :
    Triangle (DStd Z) :=
  @ShortComplex.ShortExact.singleTriangle _ _ _ (HasDerivedCategory.standard _) T hT

/-- The triangle `ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ ℱ₁[1]` of a short exact sequence of `𝒪_Z`-modules is
distinguished in `D(𝒪_Z)`, at the standard model. -/
theorem singleTriangleStd_distinguished {Z : Scheme.{u}} {T : ShortComplex Z.Modules}
    (hT : T.ShortExact) : singleTriangleStd hT ∈ distTriang (DStd Z) :=
  @ShortComplex.ShortExact.singleTriangle_distinguished _ _ _ (HasDerivedCategory.standard _) T hT

/-- A quasi-coherent module placed in degree zero lies in `D^+_{QCoh}`. -/
theorem boundedBelowQCoh_single (F : S.Modules) (hF : F.IsQuasicoherent) :
    boundedBelowQCoh S ((singleStd S).obj F) :=
  ⟨⟨0, inferInstance⟩, fun i ↦
    Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isQuasicoherent_homology_singleFunctor_obj
      0 F hF i⟩

/-- `D^+_{QCoh}` is stable under the shifts. -/
theorem boundedBelowQCoh_shift (N : DStd S) (n : ℤ) (hN : boundedBelowQCoh S N) :
    boundedBelowQCoh S (N⟦n⟧) := by
  obtain ⟨⟨c, hc⟩, hq⟩ := hN
  have : (tStd S).IsGE N c := hc
  refine ⟨⟨c - n, (tStd S).isGE_shift N c n (c - n) (by omega)⟩, fun i ↦ ?_⟩
  exact Stacks.Cohomology.ProjectionFormulaQCohDevissage.isDQCoh_shift N hq n i

/-- **The natural identification** `Hom(L, N) ≃ Hom(K, E ⊗^L Lf^*N)` on `D^+_{QCoh}(𝒪_S)`, for the
complex `L = hocolim (Rf_*R𝓗om(Kₙ, E))^∨` attached to a presentation `K = hocolim Kₙ` by perfect
objects, under the hypotheses of `exists_unit_bijective`, which the situation of
[Stacks, Tag 0DJU] supplies. -/
theorem nonempty_naturalHomIdentification [QuasiCompact f] [QuasiSeparated f]
    (hE : ∀ i : ℤ, ((hStd X i).obj E).IsQuasicoherent)
    (FK : ℕ ⥤ DStd X) [HasCoproduct FK.obj] {K : DStd X}
    {c : ∀ n, FK.obj n ⟶ K} (hK : IsHomotopyColimitWith FK K c)
    (hFK : ∀ n, IsPerfectSite (FK.obj n)) (hM : ∀ n, IsPerfectSite (stageM f E (FK.obj n)))
    [HasCoproduct (dualSystem (pushforwardSheafHomSystem f FK E)).obj] {L : DStd S}
    {d : ∀ n, (dualSystem (pushforwardSheafHomSystem f FK E)).obj n ⟶ L}
    (hL : IsHomotopyColimitWith (dualSystem (pushforwardSheafHomSystem f FK E)) L d)
    (hstage : ∀ k : ℤ, ∃ n, IsIso (((tStd X).truncGE k).map (c n)) ∧
      IsIso (((tStd S).truncGE k).map (d n)))
    (a : ℤ) (hΦ : ∀ (N : DStd S) (m : ℤ), (tStd S).IsGE N m →
      (tStd X).IsGE ((tensorPull f E).obj N) (m + a)) :
    Nonempty (ShiftedHom.NaturalHomIdentification (𝟭 (DStd S)) (tensorPull f E) L K
      (boundedBelowQCoh S)) := by
  obtain ⟨η, hη⟩ := exists_unit_bijective f E FK hK hFK hM hL hstage a hΦ (boundedBelowQCoh S)
    (fun N hN ↦ hN.1) (fun n N hN ↦ isIso_pfMap f E (FK.obj n) (hFK n) hE N hN.2)
  exact ⟨{ equiv := fun N hN ↦ AddEquiv.ofBijective
              (AddMonoidHom.mk' (fun ψ : L ⟶ (𝟭 (DStd S)).obj N ↦ η ≫ (tensorPull f E).map ψ)
                (fun x y ↦ by rw [Functor.map_add, Preadditive.comp_add])) (hη N hN)
           naturality := fun hN hN' g x ↦ by simp }⟩

/-- **Uniqueness.** Two objects with quasi-coherent cohomology carrying natural identifications
`Hom(-, N) ≃ Hom(K, E ⊗^L Lf^*N)` on `D^+_{QCoh}(𝒪_S)` are isomorphic, by an isomorphism
inducing the identifications ([Stacks, Tag 0DJS]-style canonicity). -/
theorem exists_iso_of_naturalHomIdentification {K : DStd X} {L L' : DStd S}
    (θ : ShiftedHom.NaturalHomIdentification (𝟭 (DStd S)) (tensorPull f E) L K
      (boundedBelowQCoh S))
    (θ' : ShiftedHom.NaturalHomIdentification (𝟭 (DStd S)) (tensorPull f E) L' K
      (boundedBelowQCoh S))
    (hL : ∀ q : ℤ, ((hStd S q).obj L).IsQuasicoherent)
    (hL' : ∀ q : ℤ, ((hStd S q).obj L').IsQuasicoherent) :
    ∃ φ : L' ≅ L, ∀ (N : DStd S) (hN : boundedBelowQCoh S N) (x : L ⟶ N),
      θ'.equiv N hN (φ.hom ≫ x) = θ.equiv N hN x :=
  exists_iso_of_representing (tensorPull f E) K (boundedBelowQCoh S) (fun N hN ↦ hN.1) L L'
    hL hL' (fun n ↦ boundedBelowQuasicoherent_truncGE L hL _)
    (fun n ↦ boundedBelowQuasicoherent_truncGE L' hL' _)
    (fun N hN ↦ (θ.equiv N hN).toEquiv) (fun hN hN' g x ↦ θ.naturality hN hN' g x)
    (fun N hN ↦ (θ'.equiv N hN).toEquiv) (fun hN hN' g x ↦ θ'.naturality hN hN' g x)

section Ext

variable {f E} {K : DStd X} {L : DStd S}
  (θ : ShiftedHom.NaturalHomIdentification (𝟭 (DStd S)) (tensorPull f E) L K (boundedBelowQCoh S))

/-- **The identification of `Ext`-groups** `Ext^i_{𝒪_S}(L, ℱ) ≃ Ext^i_{𝒪_X}(K, E ⊗^L Lf^*ℱ)`
for `ℱ` quasi-coherent, induced by a natural identification on `D^+_{QCoh}(𝒪_S)`. -/
def extEquiv (F : S.Modules) (hF : F.IsQuasicoherent) (i : ℤ) :
    ShiftedHom L ((singleStd S).obj F) i ≃+
      ShiftedHom K ((tensorPull f E).obj ((singleStd S).obj F)) i :=
  ShiftedHom.transport θ boundedBelowQCoh_shift ((singleStd S).obj F)
    (boundedBelowQCoh_single F hF) i

/-- The identification of `Ext`-groups is natural in the quasi-coherent module. -/
theorem extEquiv_naturality {F F' : S.Modules} (hF : F.IsQuasicoherent)
    (hF' : F'.IsQuasicoherent) (g : F ⟶ F') (i : ℤ) (x : ShiftedHom L ((singleStd S).obj F) i) :
    extEquiv θ F' hF' i (x ≫ ((singleStd S).map g)⟦i⟧') =
      extEquiv θ F hF i x ≫ ((tensorPull f E).map ((singleStd S).map g))⟦i⟧' :=
  ShiftedHom.transport_naturality θ boundedBelowQCoh_shift _ _ ((singleStd S).map g) i x

/-- The image of a shifted morphism under the identity functor is the morphism itself. -/
theorem shiftedHom_map_id {Z : Scheme.{u}} {A B : DStd Z} {n : ℤ} (δ : ShiftedHom A B n) :
    δ.map (𝟭 (DStd Z)) = δ := by
  simp [ShiftedHom.map]

/-- **The identification of `Ext`-groups is compatible with the boundary maps** of a short exact
sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of quasi-coherent modules: the boundary map on the left is
composition with the connecting morphism `ℱ₃ ⟶ ℱ₁[1]`, the one on the right composition with
its image under `E ⊗^L Lf^*(-)`, the connecting morphism of the image of the triangle. -/
theorem extEquiv_comp_singleδ {T : ShortComplex S.Modules} (hT : T.ShortExact)
    (h₁ : T.X₁.IsQuasicoherent) (h₃ : T.X₃.IsQuasicoherent) (i j : ℤ) (hij : 1 + i = j)
    (x : ShiftedHom L ((singleStd S).obj T.X₃) i) :
    extEquiv θ T.X₁ h₁ j (ShiftedHom.comp x (singleδStd hT) hij) =
      (extEquiv θ T.X₃ h₃ i x).comp (ShiftedHom.map (singleδStd hT) (tensorPull f E)) hij := by
  have h := ShiftedHom.transport_comp_map θ boundedBelowQCoh_shift (boundedBelowQCoh_single _ h₃)
    (boundedBelowQCoh_single _ h₁) (singleδStd hT) i j hij x
  rw [shiftedHom_map_id] at h
  exact h

/-- The image under `E ⊗^L Lf^*(-)` of the triangle `ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ ℱ₁[1]` of a short exact
sequence is distinguished, and its third morphism is the image of the connecting morphism: the
boundary map on the right of `extEquiv_comp_singleδ` is the boundary map of the long exact
sequence of `Ext^*_{𝒪_X}(K, -)` attached to that distinguished triangle. -/
theorem tensorPull_mapTriangle_singleTriangle (f : X ⟶ S) (E : DStd X)
    {T : ShortComplex S.Modules} (hT : T.ShortExact) :
    (tensorPull f E).mapTriangle.obj (singleTriangleStd hT) ∈ distTriang (DStd X) ∧
      ((tensorPull f E).mapTriangle.obj (singleTriangleStd hT)).mor₃ =
        ShiftedHom.map (singleδStd hT) (tensorPull f E) :=
  ⟨(tensorPull f E).map_distinguished _ (singleTriangleStd_distinguished hT), rfl⟩

end Ext

/-- **The characterization, from a presentation.** In the situation of
`nonempty_naturalHomIdentification`, with `L` having quasi-coherent cohomology, there is a
natural identification `θ : Hom(L, N) ≃ Hom(K, E ⊗^L Lf^*N)` on `D^+_{QCoh}(𝒪_S)`; the induced
identifications `Ext^i_{𝒪_S}(L, ℱ) ≃ Ext^i_{𝒪_X}(K, E ⊗^L Lf^*ℱ)`, `ℱ` quasi-coherent, are natural
in `ℱ` and compatible with boundary maps; and any `L'` with quasi-coherent cohomology carrying
such an identification is isomorphic to `L` compatibly with the identifications. -/
theorem characterization_of_presentation [QuasiCompact f] [QuasiSeparated f]
    (hE : ∀ i : ℤ, ((hStd X i).obj E).IsQuasicoherent)
    (FK : ℕ ⥤ DStd X) [HasCoproduct FK.obj] {K : DStd X}
    {c : ∀ n, FK.obj n ⟶ K} (hK : IsHomotopyColimitWith FK K c)
    (hFK : ∀ n, IsPerfectSite (FK.obj n)) (hM : ∀ n, IsPerfectSite (stageM f E (FK.obj n)))
    [HasCoproduct (dualSystem (pushforwardSheafHomSystem f FK E)).obj] {L : DStd S}
    {d : ∀ n, (dualSystem (pushforwardSheafHomSystem f FK E)).obj n ⟶ L}
    (hL : IsHomotopyColimitWith (dualSystem (pushforwardSheafHomSystem f FK E)) L d)
    (hstage : ∀ k : ℤ, ∃ n, IsIso (((tStd X).truncGE k).map (c n)) ∧
      IsIso (((tStd S).truncGE k).map (d n)))
    (hLq : ∀ q : ℤ, ((hStd S q).obj L).IsQuasicoherent)
    (a : ℤ) (hΦ : ∀ (N : DStd S) (m : ℤ), (tStd S).IsGE N m →
      (tStd X).IsGE ((tensorPull f E).obj N) (m + a)) :
    ∃ θ : ShiftedHom.NaturalHomIdentification (𝟭 (DStd S)) (tensorPull f E) L K
        (boundedBelowQCoh S),
      (∀ {F F' : S.Modules} (hF : F.IsQuasicoherent) (hF' : F'.IsQuasicoherent) (g : F ⟶ F')
          (i : ℤ) (x : ShiftedHom L ((singleStd S).obj F) i),
        extEquiv θ F' hF' i (x ≫ ((singleStd S).map g)⟦i⟧') =
          extEquiv θ F hF i x ≫ ((tensorPull f E).map ((singleStd S).map g))⟦i⟧') ∧
      (∀ {T : ShortComplex S.Modules} (hT : T.ShortExact) (h₁ : T.X₁.IsQuasicoherent)
          (h₃ : T.X₃.IsQuasicoherent) (i j : ℤ) (hij : 1 + i = j)
          (x : ShiftedHom L ((singleStd S).obj T.X₃) i),
        extEquiv θ T.X₁ h₁ j (ShiftedHom.comp x (singleδStd hT) hij) =
          (extEquiv θ T.X₃ h₃ i x).comp (ShiftedHom.map (singleδStd hT) (tensorPull f E)) hij) ∧
      ∀ (L' : DStd S), (∀ q : ℤ, ((hStd S q).obj L').IsQuasicoherent) →
        ∀ θ' : ShiftedHom.NaturalHomIdentification (𝟭 (DStd S)) (tensorPull f E) L' K
          (boundedBelowQCoh S),
        ∃ φ : L' ≅ L, ∀ (N : DStd S) (hN : boundedBelowQCoh S N) (x : L ⟶ N),
          θ'.equiv N hN (φ.hom ≫ x) = θ.equiv N hN x := by
  obtain ⟨θ⟩ := nonempty_naturalHomIdentification f E hE FK hK hFK hM hL hstage a hΦ
  exact ⟨θ, fun hF hF' g i x ↦ extEquiv_naturality θ hF hF' g i x,
    fun hT h₁ h₃ i j hij x ↦ extEquiv_comp_singleδ θ hT h₁ h₃ i j hij x,
    fun L' hL' θ' ↦ exists_iso_of_naturalHomIdentification f E θ θ' hLq hL'⟩

end Stacks.AlgebraicGeometry.RelativeExtCharacterization
