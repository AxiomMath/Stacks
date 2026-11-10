module

public import StacksFrontier.Homology.Tor.IndependenceBaseChange
import StacksFrontier.Algebra.Homology.Embedding.ExtendMap

/-!
# Tor vanishing makes derived extension of scalars of a module sit in degree zero

Let `φ : R →+* A` be a homomorphism of commutative rings in one universe and let `M` be an
`R`-module with `Tor_n^R(A, M) = 0` for every `n > 0`. Then termwise extension of scalars along
`φ` carries *every* quasi-isomorphism from a K-flat complex to `M[0]` to a quasi-isomorphism;
equivalently, `A ⊗ᴸ_R M` is `A ⊗_R M` placed in degree zero. Here `Tor_n^R(A, M)` is
`CategoryTheory.Tor`, which is computed from a projective resolution of `M` tensored with `A`.

## Main results

All declarations are in the namespace `CochainComplex.DerivedExtensionScalars`.

* `quasiIso_extendScalars_map_of_quasiIso_of_kFlat`: extension of scalars inverts one K-flat
  resolution of a complex exactly when it inverts another.
* `quasiIso_extendScalars_map_projectiveResolution_of_isZero_tor`: under the Tor hypothesis,
  extension of scalars carries a projective resolution of `M` to a quasi-isomorphism.
* `quasiIso_extendScalars_map_single_of_isZero_tor`: under the Tor hypothesis, extension of
  scalars carries any quasi-isomorphism from a K-flat complex to `M[0]` to a quasi-isomorphism.

## References

* [Stacks Project, Tag 06XZ](https://stacks.math.columbia.edu/tag/06XZ)
* [Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace CochainComplex.DerivedExtensionScalars

variable {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)

/-- `A`, viewed as an `R`-module along `φ`. -/
public abbrev baseModule : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars φ).obj (ModuleCat.of A A)

private instance : (ModuleCat.extendScalars.{u, u, u} φ).IsLeftAdjoint :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ).isLeftAdjoint

/-- **Extension of scalars inverts one K-flat resolution exactly when it inverts another.**
If `π : P ⟶ T` and `q : Q ⟶ T` are quasi-isomorphisms with `P` and `Q` K-flat, and termwise
extension of scalars along `φ` carries `q` to a quasi-isomorphism, then it carries `π` to one.

Nothing is assumed about `T`. -/
public theorem quasiIso_extendScalars_map_of_quasiIso_of_kFlat
    {P Q T : CochainComplex (ModuleCat.{u} R) ℤ}
    (hP : CochainComplex.KFlat.{u, u} P) (hQ : CochainComplex.KFlat.{u, u} Q)
    (π : P ⟶ T) (q : Q ⟶ T) [QuasiIso π] [QuasiIso q]
    (hq : QuasiIso ((CochainComplex.extendScalarsLarge.{u, u, u} φ).map q)) :
    QuasiIso ((CochainComplex.extendScalarsLarge.{u, u, u} φ).map π) := by
  let : HasDerivedCategory (ModuleCat.{u} R) := HasDerivedCategory.standard _
  let : HasDerivedCategory (ModuleCat.{u} A) := HasDerivedCategory.standard _
  let D := totalDerivedExtensionScalars.{u, u, u} φ
  have hcP : IsIso (D.comparison.app P) := D.comparison_isIso_of_kFlat P hP
  have hcQ : IsIso (D.comparison.app Q) := D.comparison_isIso_of_kFlat Q hQ
  have hD : ∀ {X Y : CochainComplex (ModuleCat.{u} R) ℤ} (f : X ⟶ Y) [QuasiIso f],
      IsIso ((DerivedCategory.Q ⋙ D.functor).map f) := fun f => by
    dsimp only [Functor.comp_map]
    infer_instance
  have hEq : IsIso ((extensionOfScalarsComplexGeneral.{u, u, u} φ).map q) := by
    change IsIso (DerivedCategory.Q.map ((CochainComplex.extendScalarsLarge.{u, u, u} φ).map q))
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
  have hT : IsIso (D.comparison.app T) := by
    have hRHS : IsIso (D.comparison.app Q ≫
        (extensionOfScalarsComplexGeneral.{u, u, u} φ).map q) := inferInstance
    rw [← D.comparison.naturality q] at hRHS
    exact IsIso.of_isIso_comp_left ((DerivedCategory.Q ⋙ D.functor).map q) _
  have hLHS : IsIso ((DerivedCategory.Q ⋙ D.functor).map π ≫ D.comparison.app T) := inferInstance
  rw [D.comparison.naturality π] at hLHS
  have : IsIso ((extensionOfScalarsComplexGeneral.{u, u, u} φ).map π) :=
    IsIso.of_isIso_comp_left (D.comparison.app P) _
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1 this

/-- Extension of scalars along `φ`, followed by restriction of scalars, is tensoring over `R`
with `A`: in each degree both are `A ⊗[R] M`, with the same `R`-action. -/
private def extensionUnderlyingIso :
    ModuleCat.extendScalars.{u, u, u} φ ⋙ ModuleCat.restrictScalars φ ≅
      tensorLeft (baseModule φ) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- A functor between categories of complexes that is isomorphic to one sending `f` to a
quasi-isomorphism also sends `f` to a quasi-isomorphism. -/
private theorem quasiIso_map_of_iso {V W : Type*} [Category V] [Category W] [Abelian V]
    [Abelian W] {c c' : ComplexShape ℕ}
    {F G : HomologicalComplex V c ⥤ HomologicalComplex W c'} (e : F ≅ G)
    {X Y : HomologicalComplex V c} (f : X ⟶ Y) [QuasiIso (G.map f)] : QuasiIso (F.map f) :=
  (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app X) (e.app Y) (e.hom.naturality f).symm)).2 ‹_›

/-- **Tor vanishing makes extension of scalars carry a projective resolution to a
quasi-isomorphism.** If `Tor_n^R(A, M) = 0` for every `n > 0` then the image under `A ⊗_R -` of
a projective resolution of `M` is a quasi-isomorphism. -/
public theorem quasiIso_extendScalars_map_projectiveResolution_of_isZero_tor
    (M : ModuleCat.{u} R) (P : ProjectiveResolution M)
    (h : ∀ n : ℕ, 0 < n → IsZero (((Tor (ModuleCat.{u} R) n).obj (baseModule φ)).obj M)) :
    QuasiIso (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
      (ComplexShape.down ℕ)).map P.π) := by
  have h0 : QuasiIso ((((tensoringLeft (ModuleCat.{u} R)).obj (baseModule φ)
      ).mapHomologicalComplex (ComplexShape.down ℕ)).map P.π) :=
    RingTheory.TorIndependence.quasiIso_tensor_map_projectiveResolution_of_isZero_Tor _ _ P h
  have h1 : QuasiIso ((((ModuleCat.extendScalars.{u, u, u} φ ⋙
      ModuleCat.restrictScalars φ).mapHomologicalComplex (ComplexShape.down ℕ))).map P.π) :=
    quasiIso_map_of_iso (NatIso.mapHomologicalComplex (extensionUnderlyingIso φ)
      (ComplexShape.down ℕ)) P.π
  have h2 : QuasiIso (((ModuleCat.restrictScalars φ).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
        (ComplexShape.down ℕ)).map P.π)) :=
    quasiIso_map_of_iso (Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.down ℕ))
      P.π
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (ModuleCat.restrictScalars φ)).1 h2

/-- **Tor vanishing makes derived extension of scalars of `M` sit in degree zero.** If
`Tor_n^R(A, M) = 0` for every `n > 0`, then termwise extension of scalars along `φ` carries
every quasi-isomorphism from a K-flat complex to `M[0]` to a quasi-isomorphism. -/
public theorem quasiIso_extendScalars_map_single_of_isZero_tor
    (M : ModuleCat.{u} R)
    (h : ∀ n : ℕ, 0 < n → IsZero (((Tor (ModuleCat.{u} R) n).obj (baseModule φ)).obj M))
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (hP : CochainComplex.KFlat.{u, u} P)
    (π : P ⟶ (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M)
    [QuasiIso π] :
    QuasiIso ((CochainComplex.extendScalarsLarge.{u, u, u} φ).map π) := by
  let P₀ := projectiveResolution M
  let Ext := ModuleCat.extendScalars.{u, u, u} φ
  let q : P₀.complex.extend ComplexShape.embeddingDownNat ⟶
      (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj M :=
    HomologicalComplex.extendMap P₀.π ComplexShape.embeddingDownNat ≫
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat M 0 0 (by simp)).hom
  have hq : QuasiIso q := by
    have : QuasiIso (HomologicalComplex.extendMap P₀.π ComplexShape.embeddingDownNat) :=
      (HomologicalComplex.quasiIso_extendMap_iff _ _).2 P₀.quasiIso
    exact quasiIso_comp _ _
  have hQ : CochainComplex.KFlat.{u, u} (P₀.complex.extend ComplexShape.embeddingDownNat) := by
    have : ∀ n, Module.Flat R ((P₀.complex.extend ComplexShape.embeddingDownNat).X n) := fun n => by
      have : Projective ((P₀.complex.extend ComplexShape.embeddingDownNat).X n) := by
        by_cases hn : ∃ m, ComplexShape.embeddingDownNat.f m = n
        · obtain ⟨m, hm⟩ := hn
          exact Projective.of_iso
            (P₀.complex.extendXIso ComplexShape.embeddingDownNat hm).symm (P₀.projective m)
        · exact (P₀.complex.isZero_extend_X ComplexShape.embeddingDownNat n
            (by simpa using hn)).projective
      have : Module.Projective R ((P₀.complex.extend ComplexShape.embeddingDownNat).X n) :=
        ModuleCat.projective_of_module_projective _
      exact Module.Flat.of_projective
    exact CochainComplex.KFlat.kFlat_of_flat _ 0
  have hExtq : QuasiIso ((CochainComplex.extendScalarsLarge.{u, u, u} φ).map q) := by
    have hπ₀ : QuasiIso ((Ext.mapHomologicalComplex (ComplexShape.down ℕ)).map P₀.π) :=
      quasiIso_extendScalars_map_projectiveResolution_of_isZero_tor φ M P₀ h
    have hext : QuasiIso ((Ext.mapHomologicalComplex (ComplexShape.up ℤ)).map
        (HomologicalComplex.extendMap P₀.π ComplexShape.embeddingDownNat)) :=
      (quasiIso_iff_of_arrow_mk_iso _ _
        (Arrow.isoMk
          (HomologicalComplex.mapHomologicalComplexExtendIso Ext P₀.complex
            ComplexShape.embeddingDownNat).symm
          (HomologicalComplex.mapHomologicalComplexExtendIso Ext _
            ComplexShape.embeddingDownNat).symm
          (HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality Ext _ P₀.π
            ComplexShape.embeddingDownNat).symm)).2
        ((HomologicalComplex.quasiIso_extendMap_iff _ _).2 inferInstance)
    change QuasiIso ((Ext.mapHomologicalComplex (ComplexShape.up ℤ)).map q)
    dsimp only [q]
    rw [Functor.map_comp]
    infer_instance
  exact quasiIso_extendScalars_map_of_quasiIso_of_kFlat φ hP hQ π q hExtq

end CochainComplex.DerivedExtensionScalars

end
