module

public import StacksFrontier.AlgebraicGeometry.Duality.CurveFamilyDualizing.TransitionUnitScalar
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity

/-!
# The transition isomorphisms of the chosen relative dualizing complexes

Let `f : X ⟶ S` and `f' : X' ⟶ S'` be flat and locally of finite presentation, and let
`g' : X' ⟶ X`, `g : S' ⟶ S` with `g' ≫ f = f' ≫ g`. An isomorphism
`α : L(g')^*ω^•_{X/S} ≅ ω^•_{X'/S'}` between the chosen relative dualizing complexes
(`AlgebraicGeometry.Scheme.Hom.relDualizingComplex`) is a *transition* for the square
(`AlgebraicGeometry.Scheme.Hom.IsRelDualizingTransition`) if, on some open `O` of the coborder
diagonal open of `f'` mapped by `g' × g'` into that of `f`, it carries the transport of the map
`ξ` of `f` along `(g', g' × g')` to the restriction of the map `ξ'` of `f'` to `O`; both
transports are read through the *normalised* identifications of the diagonal objects
(`AlgebraicGeometry.Scheme.Hom.DiagonalOpen.normDiagIso`), which are canonical.

A transition is unique when it exists, and does not depend on the open: the relation restricts
to smaller opens. The transition isomorphism of a square which has one is
`AlgebraicGeometry.Scheme.Hom.relDualizingTransition`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.IsRelDualizingTransition.unique`: transitions are unique.
* `AlgebraicGeometry.Scheme.Hom.hasRelDualizingTransition_of_isPullback`: cartesian squares have
  transitions (Stacks 0E2Y with Stacks 0E2W).
* `AlgebraicGeometry.Scheme.Hom.relDualizingTransition_id`: the identity law.
* `AlgebraicGeometry.Scheme.Hom.relDualizingTransition_comp`: the cocycle law for pasted
  squares, and `AlgebraicGeometry.Scheme.Hom.HasRelDualizingTransition.comp`.

## Implementation notes

The identification `L(𝟙)^* ≅ 𝟭` entering the relation is
`AlgebraicGeometry.Scheme.Hom.pullIdIso`, the one of the unit laws of the composition
isomorphisms of derived pullback, so that the cocycle law needs no comparison of identity
isomorphisms. All chases are generic lemmas with every object a variable: the categories of
modules occur here in several spellings with different instance terms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Duality.TwistedInverseImageDuality
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

variable {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}

/-! ### Normalised identifications -/

/-- Some identification `Lw^*Δ_*𝒪_X ≅ Δ'_*𝒪_{X'}` exists. -/
def HasDiagIso (D : DiagonalOpen f) (D' : DiagonalOpen f') (w : D'.W ⟶ D.W) : Prop :=
  Nonempty ((pull w).obj D.diagonalObject ≅ D'.diagonalObject)

/-- **The normalised identification** `Lw^*Δ_*𝒪_X ≅ Δ'_*𝒪_{X'}`, when some identification
exists: the unique one compatible with the unit maps (`IsUnitNormalized`). -/
def normDiagIso (D : DiagonalOpen f) (D' : DiagonalOpen f') (w : D'.W ⟶ D.W)
    (h : HasDiagIso D D' w) : (pull w).obj D.diagonalObject ≅ D'.diagonalObject :=
  (exists_isUnitNormalized D D' w h.some).choose

/-- The normalised identification is normalised. -/
theorem isUnitNormalized_normDiagIso (D : DiagonalOpen f) (D' : DiagonalOpen f')
    (w : D'.W ⟶ D.W) (h : HasDiagIso D D' w) :
    IsUnitNormalized D D' w (normDiagIso D D' w h) :=
  (exists_isUnitNormalized D D' w h.some).choose_spec

/-- Every normalised identification is the normalised identification. -/
theorem eq_normDiagIso {D : DiagonalOpen f} {D' : DiagonalOpen f'} {w : D'.W ⟶ D.W}
    {e : (pull w).obj D.diagonalObject ≅ D'.diagonalObject} (he : IsUnitNormalized D D' w e)
    (h : HasDiagIso D D' w) : e = normDiagIso D D' w h :=
  eq_of_isUnitNormalized D D' w he (isUnitNormalized_normDiagIso D D' w h)

/-- The normalised identification depends only on the morphism of opens. -/
theorem normDiagIso_congr {D : DiagonalOpen f} {D' : DiagonalOpen f'} {w w' : D'.W ⟶ D.W}
    (hw : w = w') (h : HasDiagIso D D' w) (h' : HasDiagIso D D' w') :
    HEq (normDiagIso D D' w h) (normDiagIso D D' w' h') := by
  subst hw
  rfl

section Three

variable {X₁ X₂ X₃ S₁ S₂ S₃ : Scheme.{u}} {f₁ : X₁ ⟶ S₁} {f₂ : X₂ ⟶ S₂} {f₃ : X₃ ⟶ S₃}
  {D₁ : DiagonalOpen f₁} {D₂ : DiagonalOpen f₂} {D₃ : DiagonalOpen f₃}

/-- Identifications compose along stacked diagonal squares. -/
theorem HasDiagIso.comp {w₂₁ : D₂.W ⟶ D₁.W} {w₃₂ : D₃.W ⟶ D₂.W} {w₃₁ : D₃.W ⟶ D₁.W}
    (h₂₁ : HasDiagIso D₁ D₂ w₂₁) (h₃₂ : HasDiagIso D₂ D₃ w₃₂) (hw : w₃₂ ≫ w₂₁ = w₃₁) :
    HasDiagIso D₁ D₃ w₃₁ :=
  ⟨diagonalPullComp D₁ D₂ D₃ w₂₁ w₃₂ w₃₁ hw h₂₁.some h₃₂.some⟩

/-- Identifications can be cancelled along stacked diagonal squares: from identifications for
`w₂₁` and for `w₃₂ ≫ w₂₁`, one for `w₃₂`. -/
theorem HasDiagIso.of_comp {w₂₁ : D₂.W ⟶ D₁.W} {w₃₂ : D₃.W ⟶ D₂.W} {w₃₁ : D₃.W ⟶ D₁.W}
    (h₂₁ : HasDiagIso D₁ D₂ w₂₁) (h₃₁ : HasDiagIso D₁ D₃ w₃₁) (hw : w₃₂ ≫ w₂₁ = w₃₁) :
    HasDiagIso D₂ D₃ w₃₂ :=
  ⟨(pull w₃₂).mapIso h₂₁.some.symm ≪≫
    (Stacks.DerivedPullback.schemeFactorIso w₃₂ w₂₁ w₃₁ hw).app D₁.diagonalObject ≪≫ h₃₁.some⟩

/-- **Normalised identifications compose.** -/
theorem diagonalPullComp_normDiagIso {w₂₁ : D₂.W ⟶ D₁.W} {w₃₂ : D₃.W ⟶ D₂.W}
    {w₃₁ : D₃.W ⟶ D₁.W} (h₂₁ : HasDiagIso D₁ D₂ w₂₁) (h₃₂ : HasDiagIso D₂ D₃ w₃₂)
    (hw : w₃₂ ≫ w₂₁ = w₃₁) (h₃₁ : HasDiagIso D₁ D₃ w₃₁) :
    diagonalPullComp D₁ D₂ D₃ w₂₁ w₃₂ w₃₁ hw (normDiagIso D₁ D₂ w₂₁ h₂₁)
      (normDiagIso D₂ D₃ w₃₂ h₃₂) = normDiagIso D₁ D₃ w₃₁ h₃₁ :=
  eq_normDiagIso (isUnitNormalized_diagonalPullComp D₁ D₂ D₃ w₂₁ w₃₂ w₃₁ hw
    (isUnitNormalized_normDiagIso D₁ D₂ w₂₁ h₂₁) (isUnitNormalized_normDiagIso D₂ D₃ w₃₂ h₃₂)) h₃₁

end Three

/-! ### Transport through the normalised identification -/

/-- **Transport of `ξ` along a diagonal square** `(g', w)` through the normalised
identification of the diagonal objects. -/
def normTransport (D : DiagonalOpen f) (D' : DiagonalOpen f') (g' : X' ⟶ X) (w : D'.W ⟶ D.W)
    (hw : w ≫ D.proj = D'.proj ≫ g') (h : HasDiagIso D D' w) (K : Std X)
    (ξ : (D.diagonalObject : Std D.W) ⟶ (pull D.proj).obj K) :
    (D'.diagonalObject : Std D'.W) ⟶ (pull D'.proj).obj ((pull g').obj K) :=
  D.xiTransport D' g' w hw (normDiagIso D D' w h) K ξ

/-- Transport is natural in `K`. -/
theorem normTransport_comp_map (D : DiagonalOpen f) (D' : DiagonalOpen f') (g' : X' ⟶ X)
    (w : D'.W ⟶ D.W) (hw : w ≫ D.proj = D'.proj ≫ g') (h : HasDiagIso D D' w) {K L : Std X}
    (ξ : (D.diagonalObject : Std D.W) ⟶ (pull D.proj).obj K) (φ : K ⟶ L) :
    D.normTransport D' g' w hw h L (ξ ≫ (pull D.proj).map φ) =
      D.normTransport D' g' w hw h K ξ ≫ (pull D'.proj).map ((pull g').map φ) :=
  D.xiTransport_comp_map D' g' w hw _ ξ φ

/-- Transport depends only on the morphisms of the square. -/
theorem normTransport_congr (D : DiagonalOpen f) (D' : DiagonalOpen f') (g' : X' ⟶ X)
    {w w' : D'.W ⟶ D.W} (e : w = w') (hw : w ≫ D.proj = D'.proj ≫ g')
    (hw' : w' ≫ D.proj = D'.proj ≫ g') (h : HasDiagIso D D' w) (h' : HasDiagIso D D' w')
    (K : Std X) (ξ : (D.diagonalObject : Std D.W) ⟶ (pull D.proj).obj K) :
    D.normTransport D' g' w hw h K ξ = D.normTransport D' g' w' hw' h' K ξ := by
  subst e
  rfl

/-- **Transport is functorial under pasting of diagonal squares.** -/
theorem normTransport_normTransport {X₁ X₂ X₃ S₁ S₂ S₃ : Scheme.{u}} {f₁ : X₁ ⟶ S₁}
    {f₂ : X₂ ⟶ S₂} {f₃ : X₃ ⟶ S₃} (D₁ : DiagonalOpen f₁) (D₂ : DiagonalOpen f₂)
    (D₃ : DiagonalOpen f₃) (g₂₁ : X₂ ⟶ X₁) (g₃₂ : X₃ ⟶ X₂) (g₃₁ : X₃ ⟶ X₁)
    (hg : g₃₂ ≫ g₂₁ = g₃₁) (w₂₁ : D₂.W ⟶ D₁.W) (w₃₂ : D₃.W ⟶ D₂.W) (w₃₁ : D₃.W ⟶ D₁.W)
    (hw : w₃₂ ≫ w₂₁ = w₃₁) (h₂₁ : w₂₁ ≫ D₁.proj = D₂.proj ≫ g₂₁)
    (h₃₂ : w₃₂ ≫ D₂.proj = D₃.proj ≫ g₃₂) (h₃₁ : w₃₁ ≫ D₁.proj = D₃.proj ≫ g₃₁)
    (e₂₁ : HasDiagIso D₁ D₂ w₂₁) (e₃₂ : HasDiagIso D₂ D₃ w₃₂) (e₃₁ : HasDiagIso D₁ D₃ w₃₁)
    (K : Std X₁) (ξ : (D₁.diagonalObject : Std D₁.W) ⟶ (pull D₁.proj).obj K) :
    D₂.normTransport D₃ g₃₂ w₃₂ h₃₂ e₃₂ _ (D₁.normTransport D₂ g₂₁ w₂₁ h₂₁ e₂₁ K ξ) ≫
        (pull D₃.proj).map ((Stacks.DerivedPullback.schemeFactorIso g₃₂ g₂₁ g₃₁ hg).hom.app K) =
      D₁.normTransport D₃ g₃₁ w₃₁ h₃₁ e₃₁ K ξ := by
  unfold normTransport
  rw [xiTransport_xiTransport D₁ D₂ D₃ g₂₁ g₃₂ g₃₁ hg w₂₁ w₃₂ w₃₁ hw h₂₁ h₃₂ h₃₁,
    diagonalPullComp_normDiagIso e₂₁ e₃₂ hw e₃₁]

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] DiagonalOpen.isOpenImmersion DiagonalOpen.isClosedImmersion

open DiagonalOpen

/-- The standard model of `D(𝒪_T)`, for `letI`. -/
local macro "stdᴰ[" T:term "]" : term =>
  `(HasDerivedCategory.standard (StrictlyPerfect.OXMod $T))

/-- The standard model of `D(𝒪_T)` at the spelling of the derived pullback, for `letI`. -/
local macro "stdSR[" T:term "]" : term =>
  `(HasDerivedCategory.standard (SheafOfModules (structureSheafRing $T)))

/-- The standard models of `D(𝒪_{T|_U})` for all opens `U` of `T`, for `letI`. -/
local macro "stdOpens[" T:term "]" : term =>
  `(fun (U : TopologicalSpace.Opens ($T).carrier) =>
    HasDerivedCategory.standard (StrictlyPerfect.OXMod (($T).restrict U.isOpenEmbedding)))

/-! ### Generic chases -/

/-- The chase behind `IsRelDualizingTransitionOn.restrict`, with every object a variable. -/
theorem transition_restrict_chase {𝒞 ℰ : Type*} [Category 𝒞] [Category ℰ] (P : ℰ ⥤ 𝒞) {Δ : 𝒞}
    {A B A₁ B₁ : ℰ} (x : Δ ⟶ P.obj A) (x' : Δ ⟶ P.obj A₁) (y : Δ ⟶ P.obj B)
    (y' : Δ ⟶ P.obj B₁) (κ₁ : A ⟶ A₁) (κ₂ : B ⟶ B₁) (φ : A₁ ⟶ B₁) (Lφ : A ⟶ B)
    (h₁ : x ≫ P.map κ₁ = x') (h₂ : y ≫ P.map κ₂ = y') (hconj : κ₁ ≫ φ = Lφ ≫ κ₂)
    (hxy : x ≫ P.map Lφ = y) : x' ≫ P.map φ = y' := by
  rw [← h₁, ← h₂, ← hxy, Category.assoc, ← P.map_comp, hconj, P.map_comp, Category.assoc]

/-- Composing with the image of an inverse undoes composing with the image of the isomorphism. -/
theorem comp_map_inv_of_comp_map_hom {𝒞 ℰ : Type*} [Category 𝒞] [Category ℰ] (P : ℰ ⥤ 𝒞)
    {A : 𝒞} {K L : ℰ} (t : A ⟶ P.obj K) (τ : A ⟶ P.obj L) (a : K ≅ L)
    (h : t ≫ P.map a.hom = τ) : τ ≫ P.map a.inv = t := by
  rw [← h, Category.assoc, ← P.map_comp, a.hom_inv_id, P.map_id, Category.comp_id]

/-- **The comparison of `L(𝟙)^* ∘ La^*` with `La^*` is the unit isomorphism of `L(𝟙)^*`.** -/
theorem schemeFactorIso_id_hom_app {Y Z : Scheme.{u}} (a : Y ⟶ Z) (h : 𝟙 Y ≫ a = a)
    (M : Std Z) :
    letI := stdSR[Y.toRingedSpace]
    (Stacks.DerivedPullback.schemeFactorIso (𝟙 Y) a a h).hom.app M =
      (Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso
        Y.toRingedSpace).hom.app ((pull a).obj M) := by
  let := stdSR[Y.toRingedSpace]
  let := stdSR[Z.toRingedSpace]
  show (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
    (𝟙 Y.toRingedSpace) a.toLRSHom.toShHom).hom.app M = _
  rw [Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackCompIsoCanonical_id_comp]
  exact Category.comp_id _

/-- Conjugating `L(𝟙)^*φ` by the comparisons of `L(𝟙)^* ∘ L(-)^*` with `L(-)^*` gives `φ`. -/
theorem schemeFactorIso_id_conj {Y Z Z' : Scheme.{u}} (a : Y ⟶ Z) (b : Y ⟶ Z')
    (ha : 𝟙 Y ≫ a = a) (hb : 𝟙 Y ≫ b = b) {K : Std Z} {L : Std Z'}
    (φ : (pull a).obj K ⟶ (pull b).obj L) :
    (Stacks.DerivedPullback.schemeFactorIso (𝟙 Y) a a ha).hom.app K ≫ φ =
      (pull (𝟙 Y)).map φ ≫ (Stacks.DerivedPullback.schemeFactorIso (𝟙 Y) b b hb).hom.app L := by
  rw [schemeFactorIso_id_hom_app, schemeFactorIso_id_hom_app]
  exact ((Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso
    Y.toRingedSpace).hom.naturality φ).symm

/-- `L(𝟙_Y)^* ≅ 𝟭`, the identification of the derived pullback along the identity entering the
unit laws of the composition isomorphisms (`derivedPullbackCompIsoCanonical_id_comp`). -/
abbrev pullIdIso (Y : Scheme.{u}) :
    letI := stdSR[Y.toRingedSpace]
    derivedPullback (𝟙 Y.toRingedSpace) ≅
      𝟭 (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))) :=
  letI := stdSR[Y.toRingedSpace]
  Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso Y.toRingedSpace

/-- **The comparison of `La^* ∘ L(𝟙)^*` with `La^*` is `La^*` of the unit isomorphism.** -/
theorem schemeFactorIso_comp_id_hom_app {Y Z : Scheme.{u}} (a : Y ⟶ Z) (h : a ≫ 𝟙 Z = a)
    (M : Std Z) :
    (Stacks.DerivedPullback.schemeFactorIso a (𝟙 Z) a h).hom.app M =
      (pull a).map ((pullIdIso Z).hom.app M) := by
  let := stdSR[Y.toRingedSpace]
  let := stdSR[Z.toRingedSpace]
  show (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
    a.toLRSHom.toShHom (𝟙 Z.toRingedSpace)).hom.app M = _
  rw [Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackCompIsoCanonical_comp_id]
  exact Category.comp_id _

/-! ### Diagonal opens of `f'` inside its coborder diagonal open -/

section Opens

variable {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]

/-- The diagonal open of `f` attached to an open `O` of its coborder diagonal open containing
the diagonal. -/
abbrev coborderOpen (O : (DiagonalOpen.coborder f).W.Opens)
    (hO : Set.range (DiagonalOpen.coborder f).diag ⊆ O) : DiagonalOpen f :=
  (DiagonalOpen.coborder f).restrictOpen O hO

omit [Flat f] in
/-- The inclusion of `O` is compatible with the first projections. -/
theorem coborderOpen_ι_proj (O : (DiagonalOpen.coborder f).W.Opens)
    (hO : Set.range (DiagonalOpen.coborder f).diag ⊆ O) :
    O.ι ≫ (DiagonalOpen.coborder f).proj = (coborderOpen f O hO).proj ≫ 𝟙 X := by
  rw [Category.comp_id]
  rfl

omit [Flat f] in
/-- The inclusion of `O` lies over the identity of `X ×_S X`. -/
theorem coborderOpen_ι_fac (O : (DiagonalOpen.coborder f).W.Opens)
    (hO : Set.range (DiagonalOpen.coborder f).diag ⊆ O) :
    O.ι ≫ (DiagonalOpen.coborder f).ι =
      (coborderOpen f O hO).ι ≫ pullbackMapOfIsPullback (isPullback_id f) :=
  DiagonalOpen.comp_ι_eq_isPullback_id _ _ _
    ((DiagonalOpen.coborder f).restrictOpenInclusion_ι _ _)

/-- The restriction of the coborder diagonal open to `O` has an identification of the diagonal
objects. -/
theorem hasDiagIso_coborderOpen (O : (DiagonalOpen.coborder f).W.Opens)
    (hO : Set.range (DiagonalOpen.coborder f).diag ⊆ O) :
    HasDiagIso (DiagonalOpen.coborder f) (coborderOpen f O hO) O.ι :=
  ⟨DiagonalOpen.baseChangeDiagonalIso (isPullback_id f) (DiagonalOpen.coborder f)
    (coborderOpen f O hO) O.ι (coborderOpen_ι_fac f O hO)⟩

/-- **The restriction of the chosen pair of `f` to `O`** (transport along the identity square
through the normalised identification). -/
def coborderOpenXi (O : (DiagonalOpen.coborder f).W.Opens)
    (hO : Set.range (DiagonalOpen.coborder f).diag ⊆ O) [LocallyOfFinitePresentation f] :
    ((coborderOpen f O hO).diagonalObject : Std (coborderOpen f O hO).W) ⟶
      (pull (coborderOpen f O hO).proj).obj ((pull (𝟙 X)).obj (relDualizingComplex f)) :=
  (DiagonalOpen.coborder f).normTransport (coborderOpen f O hO) (𝟙 X) O.ι
    (coborderOpen_ι_proj f O hO) (hasDiagIso_coborderOpen f O hO) _ (relDualizingMap f)

/-- The restriction of the chosen pair of `f` to `O` is a relative dualizing complex. -/
theorem isRelativeDualizingComplex_coborderOpenXi [LocallyOfFinitePresentation f]
    (O : (DiagonalOpen.coborder f).W.Opens)
    (hO : Set.range (DiagonalOpen.coborder f).diag ⊆ O) :
    letI := stdᴰ[RingedSpace.inverseImage S.toRingedSpace f.base]
    letI := stdOpens[RingedSpace.inverseImage S.toRingedSpace f.base]
    IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) (coborderOpen f O hO)
      (DiagonalOpen.baseChangeComplex (𝟙 X) (relDualizingComplex f)) (coborderOpenXi f O hO) := by
  exact (isRelativeDualizingComplex_relDualizing f).baseChange_of_iso (isPullback_id f)
    (coborderOpen f O hO) O.ι (coborderOpen_ι_fac f O hO)
    (normDiagIso _ _ _ (hasDiagIso_coborderOpen f O hO)).symm
    ((DiagonalOpen.coborder f).projPullIso (coborderOpen f O hO) (𝟙 X) O.ι
      (coborderOpen_ι_proj f O hO) (relDualizingComplex f))

end Opens

/-! ### The transition relation -/

section Square

variable {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}

/-- `g' × g' : X' ×_{S'} X' ⟶ X ×_S X` for a commutative square `g' ≫ f = f' ≫ g`. -/
abbrev squareProd (f : X ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X) (g : S' ⟶ S)
    (comm : g' ≫ f = f' ≫ g) : pullback f' f' ⟶ pullback f f :=
  pullback.map f' f' f f g' g' g comm.symm comm.symm

/-- A morphism of diagonal opens over `g' × g'` is compatible with the first projections. -/
theorem DiagonalOpen.proj_of_squareProd {D : DiagonalOpen f} {D' : DiagonalOpen f'}
    {g' : X' ⟶ X} {g : S' ⟶ S} {comm : g' ≫ f = f' ≫ g} {w : D'.W ⟶ D.W}
    (hw : w ≫ D.ι = D'.ι ≫ squareProd f f' g' g comm) : w ≫ D.proj = D'.proj ≫ g' := by
  simp only [DiagonalOpen.proj, ← Category.assoc, hw]
  simp

/-- Transport commutes with composing `ξ` with the image of a morphism, when `ξ` and `ξ'` are
related by it. -/
private theorem normTransport_comp_map_eq_of_comp_map_eq (D : DiagonalOpen f)
    (D' : DiagonalOpen f') (g' : X' ⟶ X) (w : D'.W ⟶ D.W) (hw : w ≫ D.proj = D'.proj ≫ g')
    (h : HasDiagIso D D' w) {K L : Std X} (ξ : (D.diagonalObject : Std D.W) ⟶ (pull D.proj).obj K)
    (ξ' : (D.diagonalObject : Std D.W) ⟶ (pull D.proj).obj L) (φ : K ⟶ L)
    (hξ : ξ ≫ (pull D.proj).map φ = ξ') :
    D.normTransport D' g' w hw h K ξ ≫ (pull D'.proj).map ((pull g').map φ) =
      D.normTransport D' g' w hw h L ξ' := by
  subst hξ
  exact (D.normTransport_comp_map D' g' w hw h ξ φ).symm

variable [Flat f] [LocallyOfFinitePresentation f] [Flat f'] [LocallyOfFinitePresentation f']

/-- **The transition relation on an open `O`** of the coborder diagonal open of `f'`, mapped by
`w` (the restriction of `g' × g'`) into the coborder diagonal open of `f`: `α` carries the
transport of the map `ξ` of `f` along `(g', w)` to the restriction of the map `ξ'` of `f'` to
`O`, both read through the normalised identifications of the diagonal objects. -/
def IsRelDualizingTransitionOn (g' : X' ⟶ X) (g : S' ⟶ S) (comm : g' ≫ f = f' ≫ g)
    (O : (DiagonalOpen.coborder f').W.Opens)
    (hO : Set.range (DiagonalOpen.coborder f').diag ⊆ O)
    (w : (coborderOpen f' O hO).W ⟶ (DiagonalOpen.coborder f).W)
    (hw : w ≫ (DiagonalOpen.coborder f).ι = (coborderOpen f' O hO).ι ≫ squareProd f f' g' g comm)
    (α : DiagonalOpen.baseChangeComplex g' (relDualizingComplex f) ≅ relDualizingComplex f') :
    Prop :=
  ∃ h : HasDiagIso (DiagonalOpen.coborder f) (coborderOpen f' O hO) w,
    (DiagonalOpen.coborder f).normTransport (coborderOpen f' O hO) g' w
        (DiagonalOpen.proj_of_squareProd hw) h _ (relDualizingMap f) ≫
      (pull (coborderOpen f' O hO).proj).map (α.hom ≫
        (pullIdIso X').inv.app (relDualizingComplex f')) =
    coborderOpenXi f' O hO

/-- `(a ≪≫ i).hom ≫ i.inv = a.hom`, with every object a variable. -/
theorem trans_hom_comp_inv {C : Type*} [Category C] {A B B' : C} (a : A ≅ B) (i : B ≅ B') :
    (a ≪≫ i).hom ≫ i.inv = a.hom := by
  simp

/-- Rewriting the morphism inside `P.map`, with every object a variable. -/
theorem comp_map_eq_of_eq {𝒞 ℰ : Type*} [Category 𝒞] [Category ℰ] (P : ℰ ⥤ 𝒞) {A : 𝒞}
    {K L : ℰ} (t : A ⟶ P.obj K) (τ : A ⟶ P.obj L) (x y : K ⟶ L) (hxy : x = y)
    (h : t ≫ P.map y = τ) : t ≫ P.map x = τ := by
  rw [hxy, h]

/-- Composing with the image of an identity, with every object a variable. -/
theorem comp_map_id_eq {𝒞 ℰ : Type*} [Category 𝒞] [Category ℰ] (P : ℰ ⥤ 𝒞) {A : 𝒞} {K : ℰ}
    (t τ : A ⟶ P.obj K) (h : t = τ) (x : K ⟶ K) (hx : x = 𝟙 K) : t ≫ P.map x = τ := by
  rw [hx, P.map_id, Category.comp_id, h]

/-- Two isomorphisms which agree after composing with a third are equal. -/
theorem iso_eq_of_symm_trans_eq {C : Type*} [Category C] {A B B' : C} (α β : A ≅ B) (e : B ≅ B')
    (h : (α ≪≫ e).symm = (β ≪≫ e).symm) : α = β := by
  have h' : α ≪≫ e = β ≪≫ e := by rw [← Iso.symm_symm_eq (α ≪≫ e), h, Iso.symm_symm_eq]
  ext
  have := congrArg Iso.hom h'
  simp only [Iso.trans_hom] at this
  exact (cancel_mono e.hom).1 this

/-- **On a fixed open, a transition is unique.** -/
theorem IsRelDualizingTransitionOn.unique {g' : X' ⟶ X} {g : S' ⟶ S} {comm : g' ≫ f = f' ≫ g}
    {O : (DiagonalOpen.coborder f').W.Opens}
    {hO : Set.range (DiagonalOpen.coborder f').diag ⊆ O}
    {w : (coborderOpen f' O hO).W ⟶ (DiagonalOpen.coborder f).W}
    {hw : w ≫ (DiagonalOpen.coborder f).ι = (coborderOpen f' O hO).ι ≫ squareProd f f' g' g comm}
    {α β : DiagonalOpen.baseChangeComplex g' (relDualizingComplex f) ≅ relDualizingComplex f'}
    (hα : IsRelDualizingTransitionOn g' g comm O hO w hw α)
    (hβ : IsRelDualizingTransitionOn g' g comm O hO w hw β) : α = β := by
  obtain ⟨h, hα⟩ := hα
  obtain ⟨h', hβ⟩ := hβ
  have R := isRelativeDualizingComplex_coborderOpenXi f' O hO
  let e := ((pullIdIso X').app (relDualizingComplex f')).symm
  have e1 := comp_map_inv_of_comp_map_hom (pull (coborderOpen f' O hO).proj) _ _ (α ≪≫ e) hα
  have e2 := comp_map_inv_of_comp_map_hom (pull (coborderOpen f' O hO).proj) _ _ (β ≪≫ e) hβ
  exact iso_eq_of_symm_trans_eq α β e (R.iso_ext_of_comp_eq e1 e2)

/-- The transition relation only depends on the morphism `w`, which is itself determined by the
square. -/
theorem IsRelDualizingTransitionOn.congr_w {g' : X' ⟶ X} {g : S' ⟶ S}
    {comm : g' ≫ f = f' ≫ g} {O : (DiagonalOpen.coborder f').W.Opens}
    {hO : Set.range (DiagonalOpen.coborder f').diag ⊆ O}
    {w w' : (coborderOpen f' O hO).W ⟶ (DiagonalOpen.coborder f).W}
    {hw : w ≫ (DiagonalOpen.coborder f).ι = (coborderOpen f' O hO).ι ≫ squareProd f f' g' g comm}
    (hw' : w' ≫ (DiagonalOpen.coborder f).ι =
      (coborderOpen f' O hO).ι ≫ squareProd f f' g' g comm)
    {α : DiagonalOpen.baseChangeComplex g' (relDualizingComplex f) ≅ relDualizingComplex f'}
    (hα : IsRelDualizingTransitionOn g' g comm O hO w hw α) :
    IsRelDualizingTransitionOn g' g comm O hO w' hw' α := by
  obtain rfl : w = w' := (cancel_mono (DiagonalOpen.coborder f).ι).1 (hw.trans hw'.symm)
  exact hα

/-- A chase for restrictions of morphisms over `g' × g'`, with every object a variable. -/
theorem comp_fac_chase {C : Type*} [Category C] {A B P Q R : C} (a : A ⟶ B) (w : B ⟶ P)
    (ι : P ⟶ Q) (b : B ⟶ R) (c : A ⟶ R) (s : R ⟶ Q) (hw : w ≫ ι = b ≫ s)
    (h : a ≫ b = c) : (a ≫ w) ≫ ι = c ≫ s := by
  rw [Category.assoc, hw, ← Category.assoc, h]

/-- A chase for the projections of restricted diagonal opens, with every object a variable. -/
theorem proj_restrict_chase {C : Type*} [Category C] {A B Q P Y : C} (ρ : A ⟶ B) (ιB : B ⟶ Q)
    (ιA : A ⟶ Q) (ι : Q ⟶ P) (p : P ⟶ Y) (h : ρ ≫ ιB = ιA) :
    ρ ≫ (ιB ≫ ι) ≫ p = ((ιA ≫ ι) ≫ p) ≫ 𝟙 Y := by
  rw [Category.comp_id, ← h]
  simp only [Category.assoc]

omit [Flat f] [LocallyOfFinitePresentation f] [Flat f'] [LocallyOfFinitePresentation f'] in
/-- The restriction of `w` to a smaller open is again over `g' × g'`. -/
theorem homOfLE_comp_fac {g' : X' ⟶ X} {g : S' ⟶ S} {comm : g' ≫ f = f' ≫ g}
    {O O' : (DiagonalOpen.coborder f').W.Opens}
    (hO : Set.range (DiagonalOpen.coborder f').diag ⊆ O)
    (hO' : Set.range (DiagonalOpen.coborder f').diag ⊆ O') (hle : O' ≤ O)
    {w : (coborderOpen f' O hO).W ⟶ (DiagonalOpen.coborder f).W}
    (hw : w ≫ (DiagonalOpen.coborder f).ι = (coborderOpen f' O hO).ι ≫ squareProd f f' g' g comm) :
    ((DiagonalOpen.coborder f').W.homOfLE hle ≫ w) ≫ (DiagonalOpen.coborder f).ι =
      (coborderOpen f' O' hO').ι ≫ squareProd f f' g' g comm := by
  have h1 : (DiagonalOpen.coborder f').W.homOfLE hle ≫ (coborderOpen f' O hO).ι =
      (coborderOpen f' O' hO').ι := by
    show _ ≫ O.ι ≫ _ = O'.ι ≫ _
    rw [← Category.assoc, Scheme.homOfLE_ι]
  exact comp_fac_chase _ w _ _ _ _ hw h1

/-- **The transition relation restricts to smaller opens.** -/
theorem IsRelDualizingTransitionOn.restrict {g' : X' ⟶ X} {g : S' ⟶ S}
    {comm : g' ≫ f = f' ≫ g} {O : (DiagonalOpen.coborder f').W.Opens}
    {hO : Set.range (DiagonalOpen.coborder f').diag ⊆ O}
    {w : (coborderOpen f' O hO).W ⟶ (DiagonalOpen.coborder f).W}
    {hw : w ≫ (DiagonalOpen.coborder f).ι = (coborderOpen f' O hO).ι ≫ squareProd f f' g' g comm}
    {α : DiagonalOpen.baseChangeComplex g' (relDualizingComplex f) ≅ relDualizingComplex f'}
    (hα : IsRelDualizingTransitionOn g' g comm O hO w hw α)
    {O' : (DiagonalOpen.coborder f').W.Opens}
    (hO' : Set.range (DiagonalOpen.coborder f').diag ⊆ O') (hle : O' ≤ O) :
    IsRelDualizingTransitionOn g' g comm O' hO' ((DiagonalOpen.coborder f').W.homOfLE hle ≫ w)
      (homOfLE_comp_fac hO hO' hle hw) α := by
  obtain ⟨h, hrel⟩ := hα
  let ρ := (DiagonalOpen.coborder f').W.homOfLE hle
  have hρι : ρ ≫ O.ι = O'.ι := Scheme.homOfLE_ι _ _
  have hρ : ρ ≫ (coborderOpen f' O hO).proj = (coborderOpen f' O' hO').proj ≫ 𝟙 X' :=
    proj_restrict_chase ρ O.ι O'.ι (DiagonalOpen.coborder f').ι (pullback.fst f' f') hρι
  have hasρ : HasDiagIso (coborderOpen f' O hO) (coborderOpen f' O' hO') ρ :=
    HasDiagIso.of_comp (hasDiagIso_coborderOpen f' O hO) (hasDiagIso_coborderOpen f' O' hO') hρι
  have hasρw : HasDiagIso (DiagonalOpen.coborder f) (coborderOpen f' O' hO') (ρ ≫ w) :=
    h.comp hasρ rfl
  refine ⟨hasρw, ?_⟩
  have h₁ := normTransport_normTransport (DiagonalOpen.coborder f) (coborderOpen f' O hO)
    (coborderOpen f' O' hO') g' (𝟙 X') g' (Category.id_comp g') w ρ (ρ ≫ w) rfl
    (DiagonalOpen.proj_of_squareProd hw) hρ
    (DiagonalOpen.proj_of_squareProd (homOfLE_comp_fac hO hO' hle hw)) h hasρ hasρw
    (relDualizingComplex f) (relDualizingMap f)
  have h₂ := normTransport_normTransport (DiagonalOpen.coborder f') (coborderOpen f' O hO)
    (coborderOpen f' O' hO') (𝟙 X') (𝟙 X') (𝟙 X') (Category.id_comp _) O.ι ρ O'.ι hρι
    (coborderOpen_ι_proj f' O hO) hρ (coborderOpen_ι_proj f' O' hO')
    (hasDiagIso_coborderOpen f' O hO) hasρ (hasDiagIso_coborderOpen f' O' hO')
    (relDualizingComplex f') (relDualizingMap f')
  have hconj := schemeFactorIso_id_conj g' (𝟙 X') (Category.id_comp g') (Category.id_comp _)
    (α.hom ≫ (pullIdIso X').inv.app (relDualizingComplex f'))
  have hxy := normTransport_comp_map_eq_of_comp_map_eq (coborderOpen f' O hO)
    (coborderOpen f' O' hO') (𝟙 X') ρ hρ hasρ _ _ _ hrel
  exact transition_restrict_chase _ _ _ _ _ _ _ _ _ h₁ h₂ hconj hxy

/-- **The transition relation**: `α` carries the transported `ξ` of `f` to the restricted `ξ'`
of `f'` on some open of the coborder diagonal open of `f'`. -/
def IsRelDualizingTransition (g' : X' ⟶ X) (g : S' ⟶ S) (comm : g' ≫ f = f' ≫ g)
    (α : DiagonalOpen.baseChangeComplex g' (relDualizingComplex f) ≅ relDualizingComplex f') :
    Prop :=
  ∃ (O : (DiagonalOpen.coborder f').W.Opens)
    (hO : Set.range (DiagonalOpen.coborder f').diag ⊆ O)
    (w : (coborderOpen f' O hO).W ⟶ (DiagonalOpen.coborder f).W)
    (hw : w ≫ (DiagonalOpen.coborder f).ι = (coborderOpen f' O hO).ι ≫ squareProd f f' g' g comm),
    IsRelDualizingTransitionOn g' g comm O hO w hw α

/-- **A transition is unique.** -/
theorem IsRelDualizingTransition.unique {g' : X' ⟶ X} {g : S' ⟶ S} {comm : g' ≫ f = f' ≫ g}
    {α β : DiagonalOpen.baseChangeComplex g' (relDualizingComplex f) ≅ relDualizingComplex f'}
    (hα : IsRelDualizingTransition g' g comm α) (hβ : IsRelDualizingTransition g' g comm β) :
    α = β := by
  obtain ⟨O₁, hO₁, w₁, hw₁, h₁⟩ := hα
  obtain ⟨O₂, hO₂, w₂, hw₂, h₂⟩ := hβ
  have hO : Set.range (DiagonalOpen.coborder f').diag ⊆ ↑(O₁ ⊓ O₂) :=
    Set.subset_inter hO₁ hO₂
  have k₁ := h₁.restrict hO (inf_le_left : O₁ ⊓ O₂ ≤ O₁)
  have k₂ := (h₂.restrict hO (inf_le_right : O₁ ⊓ O₂ ≤ O₂)).congr_w
    (homOfLE_comp_fac hO₁ hO inf_le_left hw₁)
  exact k₁.unique k₂

/-- **A transition exists as soon as the transported pair is a relative dualizing complex** on
some open `O`: then it and the restriction of the chosen pair of `f'` are uniquely isomorphic
(Stacks 0E2W). -/
theorem exists_isRelDualizingTransition_of_isRelativeDualizingComplex {g' : X' ⟶ X}
    {g : S' ⟶ S} {comm : g' ≫ f = f' ≫ g} (O : (DiagonalOpen.coborder f').W.Opens)
    (hO : Set.range (DiagonalOpen.coborder f').diag ⊆ O)
    (w : (coborderOpen f' O hO).W ⟶ (DiagonalOpen.coborder f).W)
    (hw : w ≫ (DiagonalOpen.coborder f).ι = (coborderOpen f' O hO).ι ≫ squareProd f f' g' g comm)
    (hasw : HasDiagIso (DiagonalOpen.coborder f) (coborderOpen f' O hO) w)
    (hsrc : letI := stdᴰ[RingedSpace.inverseImage S'.toRingedSpace f'.base]
      letI := stdOpens[RingedSpace.inverseImage S'.toRingedSpace f'.base]
      IsRelativeDualizingComplex f'
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S'.toRingedSpace f'.base)) (coborderOpen f' O hO)
      (DiagonalOpen.baseChangeComplex g' (relDualizingComplex f))
      ((DiagonalOpen.coborder f).normTransport (coborderOpen f' O hO) g' w
        (DiagonalOpen.proj_of_squareProd hw) hasw _ (relDualizingMap f))) :
    ∃ α, IsRelDualizingTransition g' g comm α := by
  obtain ⟨a, ha, -⟩ := IsRelativeDualizingComplex.existsUnique_iso hsrc
    (isRelativeDualizingComplex_coborderOpenXi f' O hO)
  refine ⟨a ≪≫ (pullIdIso X').app (relDualizingComplex f'), O, hO, w, hw, hasw, ?_⟩
  exact comp_map_eq_of_eq _ _ _ _ _
    (trans_hom_comp_inv a ((pullIdIso X').app (relDualizingComplex f'))) ha

/-- **Transitions exist for cartesian squares** (Stacks 0E2Y and 0E2W): the base change of the
chosen pair of `f` and the restriction of the chosen pair of `f'` are relative dualizing
complexes on `baseChangeOpen`, hence uniquely isomorphic. -/
theorem exists_isRelDualizingTransition_of_isPullback {g' : X' ⟶ X} {g : S' ⟶ S}
    (hpb : IsPullback g' f' f g) :
    ∃ α, IsRelDualizingTransition g' g hpb.w α := by
  let O := baseChangeOpen hpb
  have hO := range_diag_subset_baseChangeOpen hpb
  let w := baseChangeW hpb
  have hw : w ≫ (DiagonalOpen.coborder f).ι =
      (coborderOpen f' O hO).ι ≫ squareProd f f' g' g hpb.w := baseChangeW_ι hpb
  have hasw : HasDiagIso (DiagonalOpen.coborder f) (coborderOpen f' O hO) w :=
    ⟨DiagonalOpen.baseChangeDiagonalIso hpb (DiagonalOpen.coborder f) (coborderOpen f' O hO) w hw⟩
  have hsrc := (isRelativeDualizingComplex_relDualizing f).baseChange_of_iso hpb
    (coborderOpen f' O hO) w hw (normDiagIso _ _ _ hasw).symm
    ((DiagonalOpen.coborder f).projPullIso (coborderOpen f' O hO) g' w
      (DiagonalOpen.proj_of_squareProd hw) (relDualizingComplex f))
  exact exists_isRelDualizingTransition_of_isRelativeDualizingComplex O hO w hw hasw hsrc

/-- `g' × g'` along the identity square is the identity. -/
theorem squareProd_id (f : X ⟶ S) : squareProd f f (𝟙 X) (𝟙 S) (by simp) = 𝟙 _ := by
  ext <;> simp

/-- **The identity square has the canonical transition** `L(𝟙)^*ω^• ≅ ω^•`. -/
theorem isRelDualizingTransition_id :
    IsRelDualizingTransition (f := f) (f' := f) (𝟙 X) (𝟙 S) (by simp)
      ((pullIdIso X).app (relDualizingComplex f)) := by
  have hO : Set.range (DiagonalOpen.coborder f).diag ⊆ ↑(⊤ : (DiagonalOpen.coborder f).W.Opens) :=
    Set.subset_univ _
  have hw : (⊤ : (DiagonalOpen.coborder f).W.Opens).ι ≫ (DiagonalOpen.coborder f).ι =
      (coborderOpen f ⊤ hO).ι ≫ squareProd f f (𝟙 X) (𝟙 S) (by simp) := by
    rw [squareProd_id, Category.comp_id]
    rfl
  refine ⟨⊤, hO, _, hw, hasDiagIso_coborderOpen f ⊤ hO, ?_⟩
  exact comp_map_id_eq _ _ _ rfl _
    (Iso.hom_inv_id ((pullIdIso X).app (relDualizingComplex f)))

end Square

/-! ### Pasting transitions -/

/-- The diagonal is compatible with a morphism of diagonal opens over `g' × g'`. -/
theorem DiagonalOpen.diag_comp_of_squareProd {X S X' S' : Scheme.{u}} {f : X ⟶ S}
    {f' : X' ⟶ S'} {D : DiagonalOpen f} {D' : DiagonalOpen f'} {g' : X' ⟶ X} {g : S' ⟶ S}
    {comm : g' ≫ f = f' ≫ g} {w : D'.W ⟶ D.W}
    (hw : w ≫ D.ι = D'.ι ≫ squareProd f f' g' g comm) : D'.diag ≫ w = g' ≫ D.diag := by
  rw [← cancel_mono D.ι, Category.assoc, hw, ← Category.assoc, D'.fac, Category.assoc, D.fac]
  apply pullback.hom_ext <;> simp

/-- `g' × g'` of a pasted square is the composite of the two `g' × g'`. -/
theorem squareProd_comp {X₁ X₂ X₃ S₁ S₂ S₃ : Scheme.{u}} {f₁ : X₁ ⟶ S₁} {f₂ : X₂ ⟶ S₂}
    {f₃ : X₃ ⟶ S₃} {g₁' : X₂ ⟶ X₁} {g₁ : S₂ ⟶ S₁} (comm₁ : g₁' ≫ f₁ = f₂ ≫ g₁)
    {g₂' : X₃ ⟶ X₂} {g₂ : S₃ ⟶ S₂} (comm₂ : g₂' ≫ f₂ = f₃ ≫ g₂)
    (comm : (g₂' ≫ g₁') ≫ f₁ = f₃ ≫ g₂ ≫ g₁) :
    squareProd f₂ f₃ g₂' g₂ comm₂ ≫ squareProd f₁ f₂ g₁' g₁ comm₁ =
      squareProd f₁ f₃ (g₂' ≫ g₁') (g₂ ≫ g₁) comm := by
  apply pullback.hom_ext <;> simp

/-- The commutativity of a pasted square. -/
theorem comm_paste {X₁ X₂ X₃ S₁ S₂ S₃ : Scheme.{u}} {f₁ : X₁ ⟶ S₁} {f₂ : X₂ ⟶ S₂}
    {f₃ : X₃ ⟶ S₃} {g₁' : X₂ ⟶ X₁} {g₁ : S₂ ⟶ S₁} (comm₁ : g₁' ≫ f₁ = f₂ ≫ g₁)
    {g₂' : X₃ ⟶ X₂} {g₂ : S₃ ⟶ S₂} (comm₂ : g₂' ≫ f₂ = f₃ ≫ g₂) :
    (g₂' ≫ g₁') ≫ f₁ = f₃ ≫ g₂ ≫ g₁ := by
  rw [Category.assoc, comm₁, ← Category.assoc, comm₂, Category.assoc]

section Paste

variable {X₁ X₂ X₃ S₁ S₂ S₃ : Scheme.{u}} {f₁ : X₁ ⟶ S₁} {f₂ : X₂ ⟶ S₂} {f₃ : X₃ ⟶ S₃}
  [Flat f₁] [LocallyOfFinitePresentation f₁] [Flat f₂] [LocallyOfFinitePresentation f₂]
  [Flat f₃] [LocallyOfFinitePresentation f₃]
  {g₂' : X₃ ⟶ X₂} {g₂ : S₃ ⟶ S₂} {comm₂ : g₂' ≫ f₂ = f₃ ≫ g₂}

/-- The open of `O₂` mapped by `w₂` into `O₁`, as an open of the coborder diagonal open of
`f₃`. -/
def pasteOpen {O₂ : (DiagonalOpen.coborder f₃).W.Opens}
    (hO₂ : Set.range (DiagonalOpen.coborder f₃).diag ⊆ O₂)
    (w₂ : (coborderOpen f₃ O₂ hO₂).W ⟶ (DiagonalOpen.coborder f₂).W)
    (O₁ : (DiagonalOpen.coborder f₂).W.Opens) : (DiagonalOpen.coborder f₃).W.Opens :=
  O₂.ι ''ᵁ (w₂ ⁻¹ᵁ O₁)

omit [Flat f₂] [LocallyOfFinitePresentation f₂] [Flat f₃] [LocallyOfFinitePresentation f₃] in
/-- `pasteOpen` is contained in `O₂`. -/
theorem pasteOpen_le {O₂ : (DiagonalOpen.coborder f₃).W.Opens}
    (hO₂ : Set.range (DiagonalOpen.coborder f₃).diag ⊆ O₂)
    (w₂ : (coborderOpen f₃ O₂ hO₂).W ⟶ (DiagonalOpen.coborder f₂).W)
    (O₁ : (DiagonalOpen.coborder f₂).W.Opens) : pasteOpen hO₂ w₂ O₁ ≤ O₂ :=
  Scheme.Opens.ι_image_le _ _

omit [Flat f₂] [LocallyOfFinitePresentation f₂] [Flat f₃] [LocallyOfFinitePresentation f₃] in
/-- `pasteOpen` contains the diagonal. -/
theorem range_diag_subset_pasteOpen {O₂ : (DiagonalOpen.coborder f₃).W.Opens}
    (hO₂ : Set.range (DiagonalOpen.coborder f₃).diag ⊆ O₂)
    {w₂ : (coborderOpen f₃ O₂ hO₂).W ⟶ (DiagonalOpen.coborder f₂).W}
    (hw₂ : w₂ ≫ (DiagonalOpen.coborder f₂).ι =
      (coborderOpen f₃ O₂ hO₂).ι ≫ squareProd f₂ f₃ g₂' g₂ comm₂)
    {O₁ : (DiagonalOpen.coborder f₂).W.Opens}
    (hO₁ : Set.range (DiagonalOpen.coborder f₂).diag ⊆ O₁) :
    Set.range (DiagonalOpen.coborder f₃).diag ⊆ pasteOpen hO₂ w₂ O₁ := by
  rintro _ ⟨x, rfl⟩
  refine ⟨(coborderOpen f₃ O₂ hO₂).diag x, ?_, ?_⟩
  · show w₂ ((coborderOpen f₃ O₂ hO₂).diag x) ∈ O₁
    rw [← Scheme.Hom.comp_apply, DiagonalOpen.diag_comp_of_squareProd hw₂,
      Scheme.Hom.comp_apply]
    exact hO₁ ⟨_, rfl⟩
  · show O₂.ι ((coborderOpen f₃ O₂ hO₂).diag x) = (DiagonalOpen.coborder f₃).diag x
    have hl := IsOpenImmersion.lift_fac O₂.ι (DiagonalOpen.coborder f₃).diag
      (by simpa using hO₂)
    exact (Scheme.Hom.comp_apply (coborderOpen f₃ O₂ hO₂).diag O₂.ι x).symm.trans
      (congrArg (fun m : X₃ ⟶ (DiagonalOpen.coborder f₃).W => m x) hl)

/-- The restriction of `w₂` to `pasteOpen`, as a morphism into the restriction of the coborder
diagonal open of `f₂` to `O₁`. -/
def pasteW {O₂ : (DiagonalOpen.coborder f₃).W.Opens}
    (hO₂ : Set.range (DiagonalOpen.coborder f₃).diag ⊆ O₂)
    (w₂ : (coborderOpen f₃ O₂ hO₂).W ⟶ (DiagonalOpen.coborder f₂).W)
    (O₁ : (DiagonalOpen.coborder f₂).W.Opens) :
    (pasteOpen hO₂ w₂ O₁ : Scheme.{u}) ⟶ (O₁ : Scheme.{u}) :=
  IsOpenImmersion.lift O₁.ι
    ((DiagonalOpen.coborder f₃).W.homOfLE (pasteOpen_le hO₂ w₂ O₁) ≫ w₂) (by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      obtain ⟨y, hy, hyz⟩ := (show z.1 ∈
        (pasteOpen hO₂ w₂ O₁ : Set (DiagonalOpen.coborder f₃).W) from z.2)
      have e : y = (DiagonalOpen.coborder f₃).W.homOfLE (pasteOpen_le hO₂ w₂ O₁) z := by
        apply O₂.ι.isOpenEmbedding.injective
        rwa [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
      have hc : ((DiagonalOpen.coborder f₃).W.homOfLE (pasteOpen_le hO₂ w₂ O₁) ≫ w₂) z =
          w₂ ((DiagonalOpen.coborder f₃).W.homOfLE (pasteOpen_le hO₂ w₂ O₁) z) :=
        Scheme.Hom.comp_apply _ _ z
      rw [hc, ← e]
      exact hy)

omit [Flat f₂] [LocallyOfFinitePresentation f₂] [Flat f₃] [LocallyOfFinitePresentation f₃] in
/-- `pasteW` followed by the inclusion of `O₁` is the restriction of `w₂`. -/
theorem pasteW_ι {O₂ : (DiagonalOpen.coborder f₃).W.Opens}
    (hO₂ : Set.range (DiagonalOpen.coborder f₃).diag ⊆ O₂)
    (w₂ : (coborderOpen f₃ O₂ hO₂).W ⟶ (DiagonalOpen.coborder f₂).W)
    (O₁ : (DiagonalOpen.coborder f₂).W.Opens) :
    pasteW hO₂ w₂ O₁ ≫ O₁.ι =
      (DiagonalOpen.coborder f₃).W.homOfLE (pasteOpen_le hO₂ w₂ O₁) ≫ w₂ :=
  IsOpenImmersion.lift_fac _ _ _

/-- The chase behind `pasteW_comp_fac`, with every object a variable. -/
theorem paste_fac_chase {C : Type*} [Category C] {A'' A₁ A₂ E₁ E₂ E₃ P₁ P₂ P₃ : C}
    (p : A'' ⟶ A₁) (w₁ : A₁ ⟶ E₁) (ι₁ : E₁ ⟶ P₁) (o₁ : A₁ ⟶ E₂) (e₂ : E₂ ⟶ P₂)
    (s₁ : P₂ ⟶ P₁) (ρ : A'' ⟶ A₂) (w₂ : A₂ ⟶ E₂) (o₂ : A₂ ⟶ E₃) (e₃ : E₃ ⟶ P₃)
    (s₂ : P₃ ⟶ P₂) (o'' : A'' ⟶ E₃) (s₁₂ : P₃ ⟶ P₁)
    (hw₁ : w₁ ≫ ι₁ = (o₁ ≫ e₂) ≫ s₁) (hp : p ≫ o₁ = ρ ≫ w₂)
    (hw₂ : w₂ ≫ e₂ = (o₂ ≫ e₃) ≫ s₂) (hρ : ρ ≫ o₂ = o'') (hs : s₂ ≫ s₁ = s₁₂) :
    (p ≫ w₁) ≫ ι₁ = (o'' ≫ e₃) ≫ s₁₂ := by
  simp only [Category.assoc] at hw₁ hw₂ ⊢
  rw [hw₁, reassoc_of% hp, reassoc_of% hw₂, reassoc_of% hρ, hs]

/-- The chase behind `pasteW_fac`, with every object a variable. -/
theorem paste_fac_chase' {C : Type*} [Category C] {A'' A₁ A₂ E₂ E₃ P₂ P₃ : C}
    (p : A'' ⟶ A₁) (o₁ : A₁ ⟶ E₂) (e₂ : E₂ ⟶ P₂) (ρ : A'' ⟶ A₂) (w₂ : A₂ ⟶ E₂)
    (o₂ : A₂ ⟶ E₃) (e₃ : E₃ ⟶ P₃) (s₂ : P₃ ⟶ P₂) (o'' : A'' ⟶ E₃)
    (hp : p ≫ o₁ = ρ ≫ w₂) (hw₂ : w₂ ≫ e₂ = (o₂ ≫ e₃) ≫ s₂) (hρ : ρ ≫ o₂ = o'') :
    p ≫ o₁ ≫ e₂ = (o'' ≫ e₃) ≫ s₂ := by
  simp only [Category.assoc] at hw₂ ⊢
  rw [reassoc_of% hp, hw₂, reassoc_of% hρ]

/-- The chase behind `IsRelDualizingTransition.comp`, with every object a variable. -/
theorem cocycle_paste_chase {𝒞 ℰ : Type*} [Category 𝒞] [Category ℰ] (P : ℰ ⥤ 𝒞) {Δ : 𝒞}
    {A A₁₂ B B₂ C' C : ℰ} (x : Δ ⟶ P.obj A) (xW : Δ ⟶ P.obj A₁₂) (y : Δ ⟶ P.obj B)
    (yρ : Δ ⟶ P.obj B₂) (z : Δ ⟶ P.obj C) (s₁ : A ≅ A₁₂) (s₂ : B ⟶ B₂) (Gφ : A ⟶ B)
    (Ga : A ⟶ B₂) (a : B₂ ⟶ C') (ι : C' ⟶ C)
    (h₁ : x ≫ P.map s₁.hom = xW) (h₂ : y ≫ P.map s₂ = yρ) (hN : x ≫ P.map Gφ = y)
    (h₃ : yρ ≫ P.map (a ≫ ι) = z) (hcomp : Gφ ≫ s₂ = Ga) :
    xW ≫ P.map ((s₁.inv ≫ Ga ≫ a) ≫ ι) = z := by
  rw [← h₁, ← h₃, ← h₂, ← hN, ← hcomp]
  simp only [Category.assoc, ← P.map_comp, Iso.hom_inv_id_assoc]

/-- `G(a ≫ i⁻¹) ≫ G(i) = G(a)`, with every object a variable. -/
theorem map_comp_inv_comp_map_hom {𝒞 ℰ : Type*} [Category 𝒞] [Category ℰ] (G : ℰ ⥤ 𝒞)
    {A B B' : ℰ} (a : A ⟶ B) (i : B' ≅ B) : G.map (a ≫ i.inv) ≫ G.map i.hom = G.map a := by
  rw [← G.map_comp, Category.assoc, i.inv_hom_id, Category.comp_id]

/-- **Transitions paste** (the cocycle condition): if `α₁` is a transition for the square
`(g₁', g₁)` and `α₂` one for `(g₂', g₂)`, then `L(g₂')^*α₁` followed by `α₂`, read through the
composition isomorphism `L(g₂' ≫ g₁')^* ≅ L(g₂')^* L(g₁')^*`, is a transition for the pasted
square. -/
theorem IsRelDualizingTransition.comp {g₁' : X₂ ⟶ X₁} {g₁ : S₂ ⟶ S₁}
    {comm₁ : g₁' ≫ f₁ = f₂ ≫ g₁}
    {α₁ : DiagonalOpen.baseChangeComplex g₁' (relDualizingComplex f₁) ≅ relDualizingComplex f₂}
    {α₂ : DiagonalOpen.baseChangeComplex g₂' (relDualizingComplex f₂) ≅ relDualizingComplex f₃}
    (h₁ : IsRelDualizingTransition g₁' g₁ comm₁ α₁)
    (h₂ : IsRelDualizingTransition g₂' g₂ comm₂ α₂) :
    IsRelDualizingTransition (g₂' ≫ g₁') (g₂ ≫ g₁) (comm_paste comm₁ comm₂)
      (((Stacks.DerivedPullback.schemeFactorIso g₂' g₁' (g₂' ≫ g₁') rfl).app
        (relDualizingComplex f₁)).symm ≪≫ (pull g₂').mapIso α₁ ≪≫ α₂) := by
  obtain ⟨O₁, hO₁, w₁, hw₁, hh₁, rel₁⟩ := h₁
  obtain ⟨O₂, hO₂, w₂, hw₂, hh₂, rel₂⟩ := h₂
  have hO := range_diag_subset_pasteOpen hO₂ hw₂ hO₁
  have hle := pasteOpen_le hO₂ w₂ O₁
  obtain ⟨hρw, rel₂'⟩ := (show IsRelDualizingTransitionOn g₂' g₂ comm₂ O₂ hO₂ w₂ hw₂ α₂ from
    ⟨hh₂, rel₂⟩).restrict hO hle
  have hp := pasteW_ι hO₂ w₂ O₁
  have hasp : HasDiagIso (coborderOpen f₂ O₁ hO₁) (coborderOpen f₃ (pasteOpen hO₂ w₂ O₁) hO)
      (pasteW hO₂ w₂ O₁) :=
    HasDiagIso.of_comp (hasDiagIso_coborderOpen f₂ O₁ hO₁) hρw hp
  have hρι : (DiagonalOpen.coborder f₃).W.homOfLE hle ≫ O₂.ι = (pasteOpen hO₂ w₂ O₁).ι :=
    Scheme.homOfLE_ι _ _
  have hpfac : pasteW hO₂ w₂ O₁ ≫ (coborderOpen f₂ O₁ hO₁).ι =
      (coborderOpen f₃ (pasteOpen hO₂ w₂ O₁) hO).ι ≫ squareProd f₂ f₃ g₂' g₂ comm₂ :=
    paste_fac_chase' _ O₁.ι (DiagonalOpen.coborder f₂).ι _ w₂ O₂.ι
      (DiagonalOpen.coborder f₃).ι _ _ hp hw₂ hρι
  have hW : (pasteW hO₂ w₂ O₁ ≫ w₁) ≫ (DiagonalOpen.coborder f₁).ι =
      (coborderOpen f₃ (pasteOpen hO₂ w₂ O₁) hO).ι ≫
        squareProd f₁ f₃ (g₂' ≫ g₁') (g₂ ≫ g₁) (comm_paste comm₁ comm₂) :=
    paste_fac_chase _ w₁ (DiagonalOpen.coborder f₁).ι O₁.ι (DiagonalOpen.coborder f₂).ι _ _ w₂
      O₂.ι (DiagonalOpen.coborder f₃).ι _ _ _ hw₁ hp hw₂ hρι (squareProd_comp comm₁ comm₂ _)
  have hasW : HasDiagIso (DiagonalOpen.coborder f₁) (coborderOpen f₃ (pasteOpen hO₂ w₂ O₁) hO)
      (pasteW hO₂ w₂ O₁ ≫ w₁) := hh₁.comp hasp rfl
  refine ⟨pasteOpen hO₂ w₂ O₁, hO, _, hW, hasW, ?_⟩
  have hpproj := DiagonalOpen.proj_of_squareProd (D := coborderOpen f₂ O₁ hO₁)
    (D' := coborderOpen f₃ (pasteOpen hO₂ w₂ O₁) hO) hpfac
  have P1 := normTransport_normTransport (DiagonalOpen.coborder f₁) (coborderOpen f₂ O₁ hO₁)
    (coborderOpen f₃ (pasteOpen hO₂ w₂ O₁) hO) g₁' g₂' (g₂' ≫ g₁') rfl w₁
    (pasteW hO₂ w₂ O₁) _ rfl (DiagonalOpen.proj_of_squareProd hw₁) hpproj
    (DiagonalOpen.proj_of_squareProd hW) hh₁ hasp hasW (relDualizingComplex f₁)
    (relDualizingMap f₁)
  have P2 := normTransport_normTransport (DiagonalOpen.coborder f₂) (coborderOpen f₂ O₁ hO₁)
    (coborderOpen f₃ (pasteOpen hO₂ w₂ O₁) hO) (𝟙 X₂) g₂' g₂' (Category.comp_id g₂') O₁.ι
    (pasteW hO₂ w₂ O₁) _ hp (coborderOpen_ι_proj f₂ O₁ hO₁) hpproj
    (DiagonalOpen.proj_of_squareProd (homOfLE_comp_fac hO₂ hO hle hw₂))
    (hasDiagIso_coborderOpen f₂ O₁ hO₁) hasp hρw (relDualizingComplex f₂) (relDualizingMap f₂)
  have hN := normTransport_comp_map_eq_of_comp_map_eq (coborderOpen f₂ O₁ hO₁)
    (coborderOpen f₃ (pasteOpen hO₂ w₂ O₁) hO) g₂' (pasteW hO₂ w₂ O₁) hpproj hasp _ _ _ rel₁
  have hcomp : (pull g₂').map (α₁.hom ≫ (pullIdIso X₂).inv.app (relDualizingComplex f₂)) ≫
      (Stacks.DerivedPullback.schemeFactorIso g₂' (𝟙 X₂) g₂' (Category.comp_id g₂')).hom.app
        (relDualizingComplex f₂) = (pull g₂').map α₁.hom := by
    have e := schemeFactorIso_comp_id_hom_app g₂' (Category.comp_id g₂') (relDualizingComplex f₂)
    exact (congrArg (fun t => (pull g₂').map (α₁.hom ≫ (pullIdIso X₂).inv.app
      (relDualizingComplex f₂)) ≫ t) e).trans
      (map_comp_inv_comp_map_hom (pull g₂') α₁.hom ((pullIdIso X₂).app (relDualizingComplex f₂)))
  exact cocycle_paste_chase _ _ _ _ _ _ _ _ _ _ _ _ P1 P2 hN rel₂' hcomp

end Paste

/-! ### The transition isomorphisms -/

section Transition

variable {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
  [Flat f] [LocallyOfFinitePresentation f] [Flat f'] [LocallyOfFinitePresentation f']

/-- The square `(g', g)` has a transition isomorphism. -/
def HasRelDualizingTransition (g' : X' ⟶ X) (g : S' ⟶ S) (comm : g' ≫ f = f' ≫ g) : Prop :=
  ∃ α, IsRelDualizingTransition g' g comm α

/-- **The transition isomorphism** `L(g')^*ω^•_{X/S} ≅ ω^•_{X'/S'}` of a square which has one:
the unique isomorphism carrying the transported map `ξ` of `f` to the restricted map `ξ'` of
`f'` (`IsRelDualizingTransition`). -/
def relDualizingTransition (g' : X' ⟶ X) (g : S' ⟶ S) (comm : g' ≫ f = f' ≫ g)
    (h : HasRelDualizingTransition g' g comm) :
    DiagonalOpen.baseChangeComplex g' (relDualizingComplex f) ≅ relDualizingComplex f' :=
  h.choose

/-- The transition isomorphism is a transition. -/
theorem isRelDualizingTransition_relDualizingTransition (g' : X' ⟶ X) (g : S' ⟶ S)
    (comm : g' ≫ f = f' ≫ g) (h : HasRelDualizingTransition g' g comm) :
    IsRelDualizingTransition g' g comm (relDualizingTransition g' g comm h) :=
  h.choose_spec

/-- **Characterisation of the transition isomorphism.** -/
theorem relDualizingTransition_eq {g' : X' ⟶ X} {g : S' ⟶ S} {comm : g' ≫ f = f' ≫ g}
    (h : HasRelDualizingTransition g' g comm)
    {α : DiagonalOpen.baseChangeComplex g' (relDualizingComplex f) ≅ relDualizingComplex f'}
    (hα : IsRelDualizingTransition g' g comm α) : relDualizingTransition g' g comm h = α :=
  (isRelDualizingTransition_relDualizingTransition g' g comm h).unique hα

/-- Having a transition isomorphism only depends on the square. -/
theorem HasRelDualizingTransition.congr {g₁' g₂' : X' ⟶ X} {g₁ g₂ : S' ⟶ S} (hg' : g₁' = g₂')
    (hg : g₁ = g₂) {comm₁ : g₁' ≫ f = f' ≫ g₁} (comm₂ : g₂' ≫ f = f' ≫ g₂)
    (h : HasRelDualizingTransition g₁' g₁ comm₁) : HasRelDualizingTransition g₂' g₂ comm₂ := by
  subst hg' hg
  exact h

/-- Cartesian squares have transition isomorphisms. -/
theorem hasRelDualizingTransition_of_isPullback {g' : X' ⟶ X} {g : S' ⟶ S}
    (hpb : IsPullback g' f' f g) : HasRelDualizingTransition g' g hpb.w :=
  exists_isRelDualizingTransition_of_isPullback hpb

end Transition

section TransitionId

variable {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]

/-- The identity square has a transition isomorphism. -/
theorem hasRelDualizingTransition_id :
    HasRelDualizingTransition (f := f) (f' := f) (𝟙 X) (𝟙 S) (by simp) :=
  ⟨_, isRelDualizingTransition_id⟩

/-- **The identity law**: the transition of the identity square is `L(𝟙)^*ω^• ≅ ω^•`. -/
theorem relDualizingTransition_id (h : HasRelDualizingTransition (f := f) (f' := f) (𝟙 X) (𝟙 S)
      (by simp)) :
    relDualizingTransition (𝟙 X) (𝟙 S) _ h = (pullIdIso X).app (relDualizingComplex f) :=
  relDualizingTransition_eq h isRelDualizingTransition_id

end TransitionId

section TransitionComp

variable {X₁ X₂ X₃ S₁ S₂ S₃ : Scheme.{u}} {f₁ : X₁ ⟶ S₁} {f₂ : X₂ ⟶ S₂} {f₃ : X₃ ⟶ S₃}
  [Flat f₁] [LocallyOfFinitePresentation f₁] [Flat f₂] [LocallyOfFinitePresentation f₂]
  [Flat f₃] [LocallyOfFinitePresentation f₃]
  {g₁' : X₂ ⟶ X₁} {g₁ : S₂ ⟶ S₁} {comm₁ : g₁' ≫ f₁ = f₂ ≫ g₁}
  {g₂' : X₃ ⟶ X₂} {g₂ : S₃ ⟶ S₂} {comm₂ : g₂' ≫ f₂ = f₃ ≫ g₂}

/-- Squares with transition isomorphisms paste to a square with a transition isomorphism. -/
theorem HasRelDualizingTransition.comp (h₁ : HasRelDualizingTransition g₁' g₁ comm₁)
    (h₂ : HasRelDualizingTransition g₂' g₂ comm₂) :
    HasRelDualizingTransition (g₂' ≫ g₁') (g₂ ≫ g₁) (comm_paste comm₁ comm₂) :=
  ⟨_, (isRelDualizingTransition_relDualizingTransition g₁' g₁ comm₁ h₁).comp
    (isRelDualizingTransition_relDualizingTransition g₂' g₂ comm₂ h₂)⟩

/-- **The cocycle law**: the transition of a pasted square is `L(g₂')^*` of the first transition
followed by the second, read through `L(g₂' ≫ g₁')^* ≅ L(g₂')^* L(g₁')^*`. -/
theorem relDualizingTransition_comp (h₁ : HasRelDualizingTransition g₁' g₁ comm₁)
    (h₂ : HasRelDualizingTransition g₂' g₂ comm₂) (comm : (g₂' ≫ g₁') ≫ f₁ = f₃ ≫ g₂ ≫ g₁)
    (h : HasRelDualizingTransition (g₂' ≫ g₁') (g₂ ≫ g₁) comm) :
    relDualizingTransition (g₂' ≫ g₁') (g₂ ≫ g₁) comm h =
      ((Stacks.DerivedPullback.schemeFactorIso g₂' g₁' (g₂' ≫ g₁') rfl).app
        (relDualizingComplex f₁)).symm ≪≫
        (pull g₂').mapIso (relDualizingTransition g₁' g₁ comm₁ h₁) ≪≫
        relDualizingTransition g₂' g₂ comm₂ h₂ :=
  relDualizingTransition_eq h ((isRelDualizingTransition_relDualizingTransition g₁' g₁ comm₁
    h₁).comp (isRelDualizingTransition_relDualizingTransition g₂' g₂ comm₂ h₂))

end TransitionComp

end AlgebraicGeometry.Scheme.Hom

end
