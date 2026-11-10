module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ClauseTwoProof
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.SourceBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.TargetChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AlgebraTransportFunctorial
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassVeronese
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RelativeProjRepresentsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjF1Functor
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSquare

/-!
# The morphism `r_{ℒ,ψ}` of [Stacks, Tag 01O9] along a change of base

Let `q : X ⟶ Z` be a morphism of schemes, `𝒜` a quasi-coherent graded `𝒪_Z`-algebra, `ℒ` an
invertible `𝒪_X`-module and `ψ : q^*𝒜 ⟶ ⨁_d ℒ^{⊗ d}` a homomorphism of graded algebras, so that
[Stacks, Tag 01O9] gives `U(ψ) ⊆ X` and `r_{ℒ,ψ} : U(ψ) ⟶ Proj_Z(𝒜)`.  The same `ψ` can be read
over the base `X` itself: for a graded `𝒪_X`-algebra `𝒜₁` with an isomorphism
`Φ : 𝒜₁ ≅ q^*𝒜`, the map `ψ↓ = Φ^*(ψ) : 𝒜₁ ⟶ ⨁_d ℒ^{⊗ d}` over `𝟙_X` (`baseDescent`) is the
base change of Tag 01NT followed by the transport along `Φ`.  This file proves that the two
readings give the same open and morphisms which agree through the comparison
`Proj_X(𝒜₁) ≅ Proj_X(q^*𝒜) ⟶ Proj_Z(𝒜)` (the isomorphism of the restricted algebras followed by
the base-change morphism of [Stacks, Tag 01O3]):

* `coveringOpen_baseDescent`: `U(ψ↓) = U(ψ)`;
* `globalMorphism_baseDescent`: `r_{ℒ,ψ} = r_{ℒ,ψ↓} ≫ Proj(Φ) ≫ (base change)` on `U(ψ)`.

Both are read off clause (2) of Tag 01O9: on the opens where `ψ` is surjective in a positive
degree the two morphisms classify quadruples which correspond under Tag 01NT and the transport
along `Φ`.

## References

* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01NT](https://stacks.math.columbia.edu/tag/01NT)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

universe u

attribute [local instance] isInvertible_piece

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting

section Laws

variable {S S' T T₂ : Scheme.{u}} (g : S' ⟶ S) (f' : T ⟶ S')
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- The contraction of an iterated pullback, read against its inverse along a further pullback:
the associativity coherence `compComparison_assoc` solved for the middle factor. -/
theorem compComparison_map_inv {M : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace)}
    {N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)} (k : T₂ ⟶ T)
    (φ : (pullbackFunctor (ringedSpaceHom (f' ≫ g))).obj M ⟶ N) :
    compComparison k f' ((pullbackFunctor (ringedSpaceHom g)).obj M) ≫
        (pullbackFunctor (ringedSpaceHom k)).map (inv (compComparison f' g M) ≫ φ) =
      inv (compComparison (k ≫ f') g M) ≫ compComparison k (f' ≫ g) M ≫
        (pullbackFunctor (ringedSpaceHom k)).map φ := by
  have h2 : compComparison k f' ((pullbackFunctor (ringedSpaceHom g)).obj M) =
      inv (compComparison (k ≫ f') g M) ≫ compComparison k (f' ≫ g) M ≫
        (pullbackFunctor (ringedSpaceHom k)).map (compComparison f' g M) :=
    (IsIso.eq_inv_comp (compComparison (k ≫ f') g M)).2 (compComparison_assoc k f' g M)
  have h3 : (pullbackFunctor (ringedSpaceHom k)).map (compComparison f' g M) ≫
      (pullbackFunctor (ringedSpaceHom k)).map (inv (compComparison f' g M) ≫ φ) =
        (pullbackFunctor (ringedSpaceHom k)).map φ := by
    rw [← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id_assoc]
  exact (congrArg (· ≫ (pullbackFunctor (ringedSpaceHom k)).map
      (inv (compComparison f' g M) ≫ φ)) h2).trans
    ((Category.assoc _ _ _).trans (congrArg (inv (compComparison (k ≫ f') g M) ≫ ·)
      ((Category.assoc _ _ _).trans (congrArg (compComparison k (f' ≫ g) M ≫ ·) h3))))

/-- **The base change of Tag 01NT commutes with pullback in the test scheme**, for the maps `ψ`
read over `S'`. -/
theorem baseChangeDown_pullback_eq (ψ : Twisting (f' ≫ g) A d L) (k : T₂ ⟶ T) :
    (ψ.baseChangeDown g f' A d).pullback k =
      (show Twisting ((k ≫ f') ≫ g) A d ((pullbackFunctor (ringedSpaceHom k)).obj L) from
        ψ.pullback k).baseChangeDown g (k ≫ f') A d :=
  Twisting.ext fun i => by
    change compComparison k f' ((pullbackFunctor (ringedSpaceHom g)).obj (A.piece (i * d))) ≫
        ((pullbackFunctor (ringedSpaceHom k)).map
          (inv (compComparison f' g (A.piece (i * d))) ≫ ψ.app i) ≫ laurentPullback k L i) =
      inv (compComparison (k ≫ f') g (A.piece (i * d))) ≫
        (compComparison k (f' ≫ g) (A.piece (i * d)) ≫
          ((pullbackFunctor (ringedSpaceHom k)).map (ψ.app i) ≫ laurentPullback k L i))
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ laurentPullback k L i) (compComparison_map_inv g f' k (ψ.app i))).trans
        ((Category.assoc _ _ _).trans (congrArg (inv (compComparison (k ≫ f') g _) ≫ ·)
          (Category.assoc _ _ _))))

end Laws

section Degree

variable {T X : Scheme.{u}} {f : T ⟶ X}
  {A B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X.toRingedSpace)} {d : ℤ}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- A homomorphism of graded algebras commutes with the reindexing of degrees, after pullback. -/
theorem map_unitalHom_app_eqToHom (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B) {m m' : ℤ}
    (h : m = m') :
    (pullbackFunctor (ringedSpaceHom f)).map (Φ.app m) ≫
        (pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg B.piece h)) =
      (pullbackFunctor (ringedSpaceHom f)).map (eqToHom (congrArg A.piece h)) ≫
        (pullbackFunctor (ringedSpaceHom f)).map (Φ.app m') := by
  subst h
  simp

/-- **The transport along a homomorphism of graded algebras commutes with the transition to a
multiple of the degree.** -/
theorem algebraTransport_scale_congrDegree (Φ : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (χ : Twisting f B d L) (a : ℤ) {e : ℤ} (h : a * d = e) :
    algebraTransport Φ ((χ.scale a).congrDegree h) =
      ((algebraTransport Φ χ).scale a).congrDegree h :=
  Twisting.ext fun i => by
    simp only [algebraTransport_app, congrDegree_app, scale_app, scaleApp, Category.assoc]
    rw [reassoc_of% (map_unitalHom_app_eqToHom Φ _),
      reassoc_of% (map_unitalHom_app_eqToHom Φ _)]
    all_goals (subst h; ring)

end Degree

section BaseChangeDegree

variable {S S' T : Scheme.{u}} (g : S' ⟶ S) (f' : T ⟶ S')
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- The contraction of an iterated pullback commutes with two reindexings of degrees. -/
theorem compComparison_eqToHom_eqToHom
    {M₁ M₂ M₃ : SheafOfModules.{u} (structureRingSheaf S.toRingedSpace)}
    {N N' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)} (h₁ : M₁ = M₂) (h₂ : M₂ = M₃)
    (φ : (pullbackFunctor (ringedSpaceHom f')).obj
      ((pullbackFunctor (ringedSpaceHom g)).obj M₃) ⟶ N)
    (ψ : N ⟶ N') :
    compComparison f' g M₁ ≫
        (pullbackFunctor (ringedSpaceHom f')).map
          (eqToHom (congrArg (pullbackFunctor (ringedSpaceHom g)).obj h₁)) ≫
        (pullbackFunctor (ringedSpaceHom f')).map
          (eqToHom (congrArg (pullbackFunctor (ringedSpaceHom g)).obj h₂)) ≫ φ ≫ ψ =
      (pullbackFunctor (ringedSpaceHom (f' ≫ g))).map (eqToHom h₁) ≫
        (pullbackFunctor (ringedSpaceHom (f' ≫ g))).map (eqToHom h₂) ≫
          (compComparison f' g M₃ ≫ φ) ≫ ψ := by
  subst h₁ h₂
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp, Category.assoc]

/-- **The base change of Tag 01NT commutes with the transition to a multiple of the degree.** -/
theorem baseChangeUp_scale_congrDegree (χ : Twisting f' (baseAlgebra g A) d L) (a : ℤ) {e : ℤ}
    (h : a * d = e) :
    ((χ.scale a).congrDegree h).baseChangeUp g f' A e =
      ((χ.baseChangeUp g f' A d).scale a).congrDegree h :=
  Twisting.ext fun i => by
    simp only [baseChangeUp_app, congrDegree_app, scale_app, scaleApp]
    exact compComparison_eqToHom_eqToHom g f' (congrArg A.piece (by rw [h]))
      (congrArg A.piece (by ring)) _ _

/-- A morphism preceded by two isomorphisms is an epimorphism exactly when it is one. -/
theorem _root_.Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.epi_isIso_isIso_comp_iff
    {C : Type*} [Category C] {P Q R S' : C} (a : P ⟶ Q) (b : Q ⟶ R)
    (c : R ⟶ S') [IsIso a] [IsIso b] : Epi (a ≫ b ≫ c) ↔ Epi c :=
  ⟨fun h => by
    rw [← Category.assoc] at h
    exact epi_of_epi (a ≫ b) c, fun _ => inferInstance⟩

/-- The descent of `ψ` along Tag 01NT followed by a transport along an isomorphism is
surjective in the same degrees as `ψ`. -/
theorem epi_algebraTransport_baseChangeDown_app_iff
    {A₁ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S'.toRingedSpace)}
    (Φ : SheafOfModules.GradedAlgebra.UnitalHom A₁ (baseAlgebra g A))
    (hΦ : ∀ n : ℤ, IsIso (Φ.app n)) (Y : Twisting (f' ≫ g) A d L) (n : ℤ) :
    Epi ((algebraTransport Φ (Y.baseChangeDown g f' A d)).app n) ↔ Epi (Y.app n) := by
  rw [algebraTransport_app, baseChangeDown_app]
  have := hΦ (n * d)
  exact @Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.epi_isIso_isIso_comp_iff
    _ _ _ _ _ _ _ _ _ inferInstance (IsIso.inv_isIso (f := compComparison f' g (A.piece (n * d))))

end BaseChangeDegree

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Twisting

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist (baseChangeHom)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {Z X : Scheme.{u}} {A : SheafGradedAlgebra.{u} Z} (q : X ⟶ Z)
  {A₁ : SheafGradedAlgebra.{u} X}
  (Φ : (situationAlgebra A₁).UnitalHom (situationAlgebra (A.pullback q)))
  (hΦ : ∀ n : ℤ, IsIso (Φ.app n))
  {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]

/-- **`ψ` read over the base `X`**: for `ψ : q^*𝒜 ⟶ ⨁_d ℒ^{⊗ d}` over `q : X ⟶ Z` and an
identification `Φ : 𝒜₁ ≅ q^*𝒜` of graded `𝒪_X`-algebras, the map `𝒜₁ ⟶ ⨁_d ℒ^{⊗ d}` over `𝟙_X`:
the base change of Tag 01NT followed by the transport along `Φ`. -/
def baseDescent (ψ : Twisting q (situationAlgebra A) 1 L) :
    Twisting (𝟙 X) (situationAlgebra A₁) 1 L :=
  Twisting.algebraTransport Φ
    ((show Twisting (𝟙 X ≫ q) (situationAlgebra A) 1 L from ψ).baseChangeDown q (𝟙 X)
      (situationAlgebra A) 1)

/-- The transport along `Φ` of the base change of Tag 01NT commutes with pullback in the test
scheme. -/
private theorem algebraTransport_baseChangeDown_pullback {T W : Scheme.{u}} (f' : T ⟶ X)
    {L₀ : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L₀]
    (Y : Twisting (f' ≫ q) (situationAlgebra A) 1 L₀) (m : W ⟶ T) :
    (Twisting.algebraTransport Φ
      (Twisting.baseChangeDown q f' (situationAlgebra A) 1 Y)).pullback m =
      Twisting.algebraTransport Φ
        (Twisting.baseChangeDown q (m ≫ f') (situationAlgebra A) 1 (Y.pullback m)) :=
  (Twisting.algebraTransport_pullback Φ _ m).trans
    (congrArg (Twisting.algebraTransport Φ)
      (Twisting.baseChangeDown_pullback_eq q f' (situationAlgebra A) 1 Y m))

/-- The pullback of `ψ↓` along a morphism of schemes is the descent of the pullback of `ψ`. -/
theorem baseDescent_pullback (ψ : Twisting q (situationAlgebra A) 1 L) {W : Scheme.{u}}
    (m : W ⟶ X) :
    (baseDescent q Φ ψ).pullback m =
      Twisting.algebraTransport Φ
        (Twisting.baseChangeDown q (m ≫ 𝟙 X) (situationAlgebra A) 1 (ψ.pullback m)) :=
  algebraTransport_baseChangeDown_pullback q Φ (𝟙 X) ψ m

include hΦ in
/-- `ψ↓` and `ψ` are surjective in the same degrees over every scheme over `X`. -/
theorem epi_baseDescent_pullback_app_iff (ψ : Twisting q (situationAlgebra A) 1 L)
    {W : Scheme.{u}} (m : W ⟶ X) (n : ℤ) :
    Epi (((baseDescent q Φ ψ).pullback m).app n) ↔ Epi ((ψ.pullback m).app n) := by
  rw [baseDescent_pullback]
  exact Twisting.epi_algebraTransport_baseChangeDown_app_iff q (m ≫ 𝟙 X) _ 1 Φ hΦ _ n

include hΦ in
/-- **`U(ψ↓) = U(ψ)`.** -/
theorem coveringOpen_baseDescent (ψ : Twisting q (situationAlgebra A) 1 L) :
    (toGradedPowerMap (baseDescent q Φ ψ)).coveringOpen = (toGradedPowerMap ψ).coveringOpen := by
  ext x
  simp only [SetLike.mem_coe]
  rw [mem_coveringOpen_iff_exists_epi, mem_coveringOpen_iff_exists_epi]
  exact exists_congr fun V => exists_congr fun k => and_congr_right fun _ =>
    and_congr_right fun _ => epi_baseDescent_pullback_app_iff q Φ hΦ ψ V.ι k

/-- The base change of Tag 01NT of the transport back of the transition of `ψ↓` to a multiple
of the degree is the transition of `ψ`. -/
theorem baseChangeUp_baseDescent_scale {W : Scheme.{u}} (m : W ⟶ X)
    {L₀ : SheafOfModules.{u} (structureRingSheaf W.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible W.toRingedSpace.presheaf (isSheafStruct W) L₀]
    (Y : Twisting (m ≫ q) (situationAlgebra A) 1 L₀) (k : ℤ) (h : k * 1 = k) :
    Twisting.baseChangeUp q m (situationAlgebra A) k
        (Twisting.algebraTransport (unitalHomInverse Φ hΦ)
          (((Twisting.algebraTransport Φ
            (Twisting.baseChangeDown q m (situationAlgebra A) 1 Y)).scale k).congrDegree h)) =
      (Y.scale k).congrDegree h :=
  (congrArg (Twisting.baseChangeUp q m (situationAlgebra A) k)
    ((congrArg (Twisting.algebraTransport (unitalHomInverse Φ hΦ))
      (Twisting.algebraTransport_scale_congrDegree Φ
        (Twisting.baseChangeDown q m (situationAlgebra A) 1 Y) k h).symm).trans
      (Twisting.algebraTransport_unitalHomInverse_algebraTransport Φ hΦ _))).trans
    ((Twisting.baseChangeUp_scale_congrDegree q m (situationAlgebra A) 1
      (Twisting.baseChangeDown q m (situationAlgebra A) 1 Y) k h).trans
      (congrArg (fun t => (t.scale k).congrDegree h)
        (Twisting.baseChangeUp_baseChangeDown q m (situationAlgebra A) 1 Y)))

/-- **On a scheme over `U(ψ)` where `ψ` is surjective in degree `k`, the quadruples attached to
`ψ` and to `ψ↓` correspond** under the base change of Tag 01NT and the transport along `Φ⁻¹`. -/
theorem baseChangeUp_restrictQuadruple_baseDescent (ψ : Twisting q (situationAlgebra A) 1 L)
    {W : Scheme.{u}} (q₀ : W ⟶ X) (k : ℕ) [Epi ((ψ.pullback q₀).app (k : ℤ))]
    [Epi (((baseDescent q Φ ψ).pullback q₀).app (k : ℤ))]
    [Epi (((ψ.pullback q₀).pullback (⊤ : W.Opens).ι).app (k : ℤ))]
    [Epi ((((baseDescent q Φ ψ).pullback q₀).pullback (⊤ : W.Opens).ι).app (k : ℤ))] :
    (Quadruple.algebraTransport (unitalHomInverse Φ hΦ) (isIso_unitalHomInverse_app Φ hΦ)
        (restrictQuadruple ((baseDescent q Φ ψ).pullback q₀) ⊤ k)).baseChangeUp q
        ((⊤ : W.Opens).ι ≫ q₀ ≫ 𝟙 X) (situationAlgebra A) (k : ℤ) =
      restrictQuadruple (ψ.pullback q₀) ⊤ k := by
  have hpb : ((baseDescent q Φ ψ).pullback q₀).pullback (⊤ : W.Opens).ι =
      Twisting.algebraTransport Φ (Twisting.baseChangeDown q ((⊤ : W.Opens).ι ≫ q₀ ≫ 𝟙 X)
        (situationAlgebra A) 1 ((ψ.pullback q₀).pullback (⊤ : W.Opens).ι)) :=
    (congrArg (fun t => t.pullback (⊤ : W.Opens).ι) (baseDescent_pullback q Φ ψ q₀)).trans
      (algebraTransport_baseChangeDown_pullback q Φ (q₀ ≫ 𝟙 X) (ψ.pullback q₀) _)
  refine Quadruple.ext rfl fun i => heq_of_eq ?_
  refine congrArg (fun t => Twisting.app t i) ?_
  change Twisting.baseChangeUp q ((⊤ : W.Opens).ι ≫ q₀ ≫ 𝟙 X) (situationAlgebra A) (k : ℤ)
      (Twisting.algebraTransport (unitalHomInverse Φ hΦ)
        (((((baseDescent q Φ ψ).pullback q₀).pullback (⊤ : W.Opens).ι).scale (k : ℤ)).congrDegree
          (mul_one (k : ℤ)))) =
    ((((ψ.pullback q₀).pullback (⊤ : W.Opens).ι)).scale (k : ℤ)).congrDegree (mul_one (k : ℤ))
  rw [hpb]
  exact baseChangeUp_baseDescent_scale q Φ hΦ ((⊤ : W.Opens).ι ≫ q₀ ≫ 𝟙 X)
    ((ψ.pullback q₀).pullback (⊤ : W.Opens).ι) (k : ℤ) (mul_one (k : ℤ))

/-- **`r_{ℒ,ψ} = r_{ℒ,ψ↓} ≫ Proj(Φ) ≫ (base change)`** on `U(ψ) = U(ψ↓)`: the morphism of
[Stacks, Tag 01O9] of `ψ` over `Z` is that of `ψ↓` over `X`, followed by the isomorphism
`Proj_X(𝒜₁) ≅ Proj_X(q^*𝒜)` of `Φ` and the base-change morphism of [Stacks, Tag 01O3]. -/
theorem globalMorphism_baseDescent (ψ : Twisting q (situationAlgebra A) 1 L) :
    X.homOfLE (coveringOpen_baseDescent q Φ hΦ ψ).ge ≫
        (toGradedPowerMap (baseDescent q Φ ψ)).globalMorphism (relativeProj A₁) ≫
          (relativeProjCongr Φ hΦ).hom ≫ baseChangeHom A q =
      (toGradedPowerMap ψ).globalMorphism (relativeProj A) := by
  set U := (toGradedPowerMap ψ).coveringOpen
  let O : PositiveSection A → U.toScheme.Opens := fun p =>
    U.ι ⁻¹ᵁ (toGradedPowerMap ψ).openOfPositiveSection p
  have hO : IsOpenCover O := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨p, hp⟩ :=
      (toGradedPowerMap ψ).exists_mem_openOfPositiveSection_of_mem_coveringOpen y.2
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, hp⟩
  refine Scheme.Cover.hom_ext (U.toScheme.openCoverOfIsOpenCover O hO) _ _ fun p => ?_
  change (O p).ι ≫ _ = (O p).ι ≫ _
  let q₀ : (O p).toScheme ⟶ X := (O p).ι ≫ U.ι
  have : Epi ((ψ.pullback q₀).app ((p.deg + 1 : ℕ) : ℤ)) :=
    epi_pullback_app_of_preimage_eq_top ψ q₀ p (top_unique fun w _ => w.2)
  have : Epi (((baseDescent q Φ ψ).pullback q₀).app ((p.deg + 1 : ℕ) : ℤ)) :=
    (epi_baseDescent_pullback_app_iff q Φ hΦ ψ q₀ _).2 inferInstance
  have : Epi (((ψ.pullback q₀).pullback (⊤ : (O p).toScheme.Opens).ι).app
      ((p.deg + 1 : ℕ) : ℤ)) := Twisting.epi_pullbackApp _ _ _ inferInstance
  have : Epi ((((baseDescent q Φ ψ).pullback q₀).pullback (⊤ : (O p).toScheme.Opens).ι).app
      ((p.deg + 1 : ℕ) : ℤ)) := Twisting.epi_pullbackApp _ _ _ inferInstance
  obtain ⟨h₁, e₁⟩ := clauseTwo_of_epi_pullback ψ q₀ (Nat.succ_pos p.deg)
  obtain ⟨h₂, e₂⟩ := clauseTwo_of_epi_pullback (baseDescent q Φ ψ) q₀ (Nat.succ_pos p.deg)
  have l₁ : IsOpenImmersion.lift U.ι q₀ h₁ = (O p).ι := by
    rw [← cancel_mono U.ι, IsOpenImmersion.lift_fac]
  have l₂ : IsOpenImmersion.lift (toGradedPowerMap (baseDescent q Φ ψ)).coveringOpen.ι q₀ h₂ =
      (O p).ι ≫ X.homOfLE (coveringOpen_baseDescent q Φ hΦ ψ).ge := by
    rw [← cancel_mono (toGradedPowerMap (baseDescent q Φ ψ)).coveringOpen.ι,
      IsOpenImmersion.lift_fac, Category.assoc, Scheme.homOfLE_ι]
  rw [l₁] at e₁
  rw [l₂] at e₂
  have : IsIso (⊤ : (O p).toScheme.Opens).ι := (Scheme.topIso (O p).toScheme).isIso_hom
  rw [← cancel_epi (⊤ : (O p).toScheme.Opens).ι, e₁]
  have e₃ := congrArg (· ≫ (relativeProjCongr Φ hΦ).hom ≫ baseChangeHom A q) e₂
  simp only [Category.assoc] at e₃
  refine e₃.trans ?_
  rw [← Category.assoc, F.classifyingMorphism_comp_relativeProjCongr,
    ← classifyingMorphism_baseChangeUp]
  exact congrArg (F.classifyingMorphism A)
    (congrArg (F.mk _ _) (baseChangeUp_restrictQuadruple_baseDescent q Φ hΦ ψ q₀ (p.deg + 1)))

/-- **A map `𝒜₁ ⟶ ⨁_d ℒ^{⊗ d}` over `𝟙_X` read over the base `Z`**: the transport along `Φ⁻¹`
followed by the base change of Tag 01NT, the inverse construction to `baseDescent`. -/
def baseAscent (χ : Twisting (𝟙 X) (situationAlgebra A₁) 1 L) :
    Twisting q (situationAlgebra A) 1 L :=
  Twisting.baseChangeUp q (𝟙 X) (situationAlgebra A) 1
    (Twisting.algebraTransport (unitalHomInverse Φ hΦ) χ)

/-- `baseDescent` undoes `baseAscent`. -/
theorem baseDescent_baseAscent (χ : Twisting (𝟙 X) (situationAlgebra A₁) 1 L) :
    baseDescent q Φ (baseAscent q Φ hΦ χ) = χ :=
  (congrArg (Twisting.algebraTransport Φ)
    ((Twisting.baseChangeEquiv q (𝟙 X) (situationAlgebra A) 1).symm_apply_apply
      (Twisting.algebraTransport (unitalHomInverse Φ hΦ) χ))).trans
    (Twisting.algebraTransport_algebraTransport_unitalHomInverse Φ hΦ χ)

/-- `globalMorphism_baseDescent`, for a map over `𝟙_X` known to be `ψ↓`. -/
theorem globalMorphism_of_eq_baseDescent (ψ : Twisting q (situationAlgebra A) 1 L)
    (χ : Twisting (𝟙 X) (situationAlgebra A₁) 1 L) (hχ : baseDescent q Φ ψ = χ) :
    ∃ h : (toGradedPowerMap ψ).coveringOpen ≤ (toGradedPowerMap χ).coveringOpen,
      X.homOfLE h ≫ (toGradedPowerMap χ).globalMorphism (relativeProj A₁) ≫
          (relativeProjCongr Φ hΦ).hom ≫ baseChangeHom A q =
        (toGradedPowerMap ψ).globalMorphism (relativeProj A) := by
  subst hχ
  exact ⟨_, globalMorphism_baseDescent q Φ hΦ ψ⟩

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
