module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Yoneda
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEqualizerRepresents

/-!
# The diagonal fibre of Artin's contraction functor as a closed subscheme

Two pieces of the proof of Stacks 0GHF which do not involve Stacks 0GHE.

* `CategoryTheory.isPullback_diag_of_factors_iff`: for a presheaf `F`, two elements
  `t₁, t₂ ∈ F(a)` and a monomorphism `e : b ⟶ a` through which exactly the morphisms equalizing
  `t₁` and `t₂` factor, the representable presheaf of `b` is the fibre product of the diagonal
  `F ⟶ F × F` with `(t₁, t₂) : h_a ⟶ F × F`. This is how "the diagonal is representable by
  closed immersions" is checked.
* `AlgebraicGeometry.Artin.ContractionEqualizer.exists_isClosedImmersion_factors_iff`: in the
  situation of Stacks 0GHD over `V`, an algebraic space over `V` whose structure morphism is a
  closed immersion and which represents `F ×_{Δ, F × F} V` on locally Noetherian schemes over `V`
  (`AlgebraicGeometry.Artin.ContractionEqualizer.diagonalFibre`) is a closed subscheme of `V`
  through which a morphism `φ : A ⟶ V` from a locally Noetherian scheme factors exactly when
  the two triples restrict to the same element of `F(A)`.

## References

* [Stacks Project, Tag 0GHD](https://stacks.math.columbia.edu/tag/0GHD)
* [Stacks Project, Tag 0GHF](https://stacks.math.columbia.edu/tag/0GHF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u₁ u

namespace CategoryTheory

variable {C : Type u₁} [Category.{v} C]

/-- A commutative square of functors is cartesian as soon as it is cartesian after evaluation
at every object. -/
theorem isPullback_of_isPullback_app {D : Type*} [Category D]
    {P A T R : C ⥤ D} (f : P ⟶ A) (g : P ⟶ T) (h : A ⟶ R) (k : T ⟶ R)
    (hsq : ∀ U, IsPullback (f.app U) (g.app U) (h.app U) (k.app U)) :
    IsPullback f g h k := by
  have hw : f ≫ h = g ≫ k := NatTrans.ext (funext fun U => (hsq U).w)
  exact IsPullback.of_isLimit (c := PullbackCone.mk f g hw) <| evaluationJointlyReflectsLimits _
    fun U => (PullbackCone.isLimitMapConeEquiv _ ((evaluation C D).obj U)).symm (hsq U).isLimit

/-- Let `F` be a presheaf, `t₁, t₂ ∈ F(a)` and `e : b ⟶ a` a monomorphism such that a morphism
`φ : A ⟶ a` factors through `e` exactly when `φ^* t₁ = φ^* t₂`. Then the representable presheaf
of `b` is the fibre product of the diagonal `F ⟶ F × F` and of `(t₁, t₂) : h_a ⟶ F × F`, with
`h_e` as the projection to `h_a`. -/
theorem isPullback_diag_of_factors_iff (F : Cᵒᵖ ⥤ Type (max w v)) {a b : C} (e : b ⟶ a) [Mono e]
    (t₁ t₂ : F.obj (op a))
    (h : ∀ ⦃A : C⦄ (φ : A ⟶ a), (∃ ψ : A ⟶ b, ψ ≫ e = φ) ↔ F.map φ.op t₁ = F.map φ.op t₂) :
    IsPullback (uliftYonedaEquiv.{w}.symm (F.map e.op t₁)) (uliftYoneda.{w}.map e) (diag F)
      (prod.lift (uliftYonedaEquiv.{w}.symm t₁) (uliftYonedaEquiv.{w}.symm t₂)) := by
  have hw : uliftYonedaEquiv.{w}.symm (F.map e.op t₁) ≫ diag F =
      uliftYoneda.{w}.map e ≫ prod.lift (uliftYonedaEquiv.{w}.symm t₁)
        (uliftYonedaEquiv.{w}.symm t₂) := by
    have he : F.map e.op t₁ = F.map e.op t₂ := (h e).1 ⟨𝟙 b, Category.id_comp e⟩
    ext : 1
    · simp only [Category.assoc, prod.lift_fst, Category.comp_id]
      rw [uliftYonedaEquiv_symm_map]
      rfl
    · simp only [Category.assoc, prod.lift_snd, Category.comp_id]
      rw [he, uliftYonedaEquiv_symm_map]
      rfl
  have hl : ∀ {G : Cᵒᵖ ⥤ Type (max w v)} (g₁ g₂ : G ⟶ F) (U : Cᵒᵖ) (x : G.obj U),
      (prod.fst : F ⨯ F ⟶ F).app U ((prod.lift g₁ g₂).app U x) = g₁.app U x ∧
      (prod.snd : F ⨯ F ⟶ F).app U ((prod.lift g₁ g₂).app U x) = g₂.app U x := fun g₁ g₂ U x =>
    ⟨by rw [← FunctorToTypes.comp, prod.lift_fst], by rw [← FunctorToTypes.comp, prod.lift_snd]⟩
  apply isPullback_of_isPullback_app
  intro U
  rw [Types.isPullback_iff]
  refine ⟨congr_app hw U, ?_, ?_⟩
  · rintro ⟨x⟩ ⟨y⟩ ⟨-, hxy⟩
    exact congrArg ULift.up ((cancel_mono e).1 (congrArg ULift.down hxy))
  · intro x₂ x₃ hx
    have h₁ : x₂ = F.map x₃.down.op t₁ :=
      (hl (𝟙 F) (𝟙 F) U x₂).1.symm.trans ((congrArg _ hx).trans (hl _ _ U x₃).1)
    have h₂ : x₂ = F.map x₃.down.op t₂ :=
      (hl (𝟙 F) (𝟙 F) U x₂).2.symm.trans ((congrArg _ hx).trans (hl _ _ U x₃).2)
    obtain ⟨ψ, hψ⟩ := (h x₃.down).2 (h₁.symm.trans h₂)
    refine ⟨ULift.up ψ, ?_, ?_⟩
    · rw [h₁, ← hψ]
      simp
    · exact congrArg ULift.up hψ

end CategoryTheory

namespace AlgebraicGeometry.Artin.ContractionEqualizer

open ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {c : ContractionSituation B S hS} {V : BigFppfOver B S hS}
    (d : ContractionEqualizer c V)

/-- For `φ : A ⟶ V`, the two triples restrict to the same element of `F(A)` exactly when they
restrict to the same element over `A` viewed as an object over `V`. -/
theorem mapTriple_eq_iff_toV {A : BigFppfOver B S hS} (φ : A ⟶ V) :
    mapTriple c φ d.t₁ = mapTriple c φ d.t₂ ↔
      mapTriple c (toV (Over.mk φ.left)) d.t₁ = mapTriple c (toV (Over.mk φ.left)) d.t₂ := by
  let i : A ≅ (Over.map V.hom).obj (Over.mk φ.left) :=
    Over.isoMk (Iso.refl _) (by simp [Over.w φ])
  have hφ : φ = i.hom ≫ toV (Over.mk φ.left) := Over.OverMorphism.ext (by simp [i])
  have h₀ : ∀ t : Triple c V,
      mapTriple c φ t = mapTriple c i.hom (mapTriple c (toV (Over.mk φ.left)) t) := fun t => by
    rw [← mapTriple_comp]
    exact congrArg (mapTriple c · t) hφ
  have h₁ : ∀ t : Triple c V, mapTriple c (toV (Over.mk φ.left)) t =
      mapTriple c i.inv (mapTriple c φ t) := fun t => by
    rw [h₀, ← mapTriple_comp, i.inv_hom_id, mapTriple_id]
  exact ⟨fun h => by rw [h₁, h₁ d.t₂, h], fun h => by rw [h₀, h₀ d.t₂, h]⟩

/-- Let `E` be an algebraic space over `V` whose structure morphism is a closed immersion and
which represents the fibre `F ×_{Δ, F × F} V` on locally Noetherian schemes over `V`. Then
`E` is a closed subscheme `e : b ⟶ V`, and a morphism `φ : A ⟶ V` from a locally Noetherian
scheme factors through `e` exactly when the two triples restrict to the same element of `F(A)`. -/
theorem exists_isClosedImmersion_factors_iff
    {E : (BigFppfOver B V.left.obj V.left.property)ᵒᵖ ⥤ Type u}
    (α : morOnLocallyNoetherian B V.left.obj V.left.property E ≅ d.diagonalFibre)
    (hpE : Space.IsClosedImmersion B V.left.obj V.left.property (terminal.from E)) :
    ∃ (b : BigFppfOver B S hS) (e : b ⟶ V),
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map e) ∧
      ∀ (A : BigFppfOver B S hS), IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj A) →
        ∀ φ : A ⟶ V, (∃ ψ : A ⟶ b, ψ ≫ e = φ) ↔ mapTriple c φ d.t₁ = mapTriple c φ d.t₂ := by
  let T₀ : BigFppfOver B V.left.obj V.left.property := Over.mk (𝟙 (B.obj V.left.property))
  have hT₀ : IsTerminal (yoneda.obj T₀) := Over.mkIdTerminal.isTerminalObj yoneda _
  have : IsIso (terminal.from (yoneda.obj T₀)) :=
    isIso_of_isTerminal hT₀ terminalIsTerminal _
  obtain ⟨b', snd, fst, hpb⟩ := hpE.1 (terminal.from (yoneda.obj T₀))
  have : IsIso fst := hpb.isIso_fst_of_isIso
  refine ⟨(Over.map V.hom).obj b', toV b', ?_, ?_⟩
  · have h : snd.left = b'.hom := (Category.comp_id _).symm.trans (Over.w snd)
    show _root_.AlgebraicGeometry.IsClosedImmersion (B.inclusion.map b'.hom)
    rw [← h]
    exact hpE.2 _ fst snd hpb
  · intro A hA φ
    rw [d.mapTriple_eq_iff_toV φ]
    let A' : LocallyNoetherianOver B V.left.obj V.left.property := ⟨Over.mk φ.left, hA⟩
    constructor
    · rintro ⟨ψ, hψ⟩
      let ψ' : Over.mk φ.left ⟶ b' :=
        Over.homMk ψ.left (by simpa using congrArg CommaMorphism.left hψ)
      let y := α.hom.app (op A') ⟨fst.app (op A'.obj) ψ'⟩
      exact y.2.1.symm.trans y.2.2
    · intro h
      let y : d.diagonalFibre.obj (op A') := ⟨mapTriple c (toV _) d.t₁, rfl, h⟩
      let ψ' : Over.mk φ.left ⟶ b' := (inv fst).app (op A'.obj) (α.inv.app (op A') y).down
      refine ⟨Over.homMk ψ'.left ?_, Over.OverMorphism.ext ?_⟩
      · have := Over.w ψ'
        simp only [Over.mk_hom] at this
        simp [← Category.assoc, this, Over.w φ]
      · simp [Over.w ψ']

end AlgebraicGeometry.Artin.ContractionEqualizer

