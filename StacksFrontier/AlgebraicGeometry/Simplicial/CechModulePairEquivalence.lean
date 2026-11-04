module

public import StacksFrontier.AlgebraicGeometry.Simplicial.CechModulePairDescentData

/-!
# Descent data relative to `{f}` are pairs on `(X/S)_•`

Let `f : X ⟶ S` be a morphism of schemes and `(X/S)_•` the simplicial scheme of Stacks 024A.
A descent datum relative to the one-element family `{f}` is a module `M` on `X` with an
isomorphism `pr_0^* M ≅ pr_1^* M` on `X ×_S X` satisfying the cocycle condition; a pair on
`(X/S)_•` in the sense of Stacks 07TH is a module `F` on `(X/S)_0` with an isomorphism
`d¹_1^* F ≅ d¹_0^* F` satisfying the cocycle condition. Pulling back along the vertex
`(X/S)_0 ⟶ X`, an isomorphism, identifies the two. Combined with Stacks 07TH and 0D7M for the
total Zariski site this identifies quasi-coherent descent data relative to `{f}` with the
quasi-coherent modules on `((X/S)_•)_Zar`, which is the identification the proof of Stacks 07TL
uses.

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.cechDescentDataToPair`: the functor from descent data over
  the chosen fibre products `(X/S)_1`, `(X/S)_2` to pairs on `(X/S)_•`; it is an equivalence.
* `AlgebraicGeometry.SimplicialScheme.descentDataEquivPair`: descent data relative to `{f}` are
  the pairs on `(X/S)_•`.
* `AlgebraicGeometry.SimplicialScheme.quasicoherentDescentDataEquivZariski`: quasi-coherent
  descent data relative to `{f}` are the quasi-coherent modules on the total Zariski site of
  `(X/S)_•`.

## Implementation notes

The descent data are taken in the form of Mathlib's
`CategoryTheory.Pseudofunctor.DescentData'` over the chosen fibre products of
`AlgebraicGeometry.SimplicialScheme.cechChosenPullback`, which
`CategoryTheory.Pseudofunctor.DescentData'.descentDataEquivalence` identifies with
`CategoryTheory.Pseudofunctor.DescentData`. The normalization along the diagonal, which descent
data carry and pairs do not, is a consequence of the cocycle condition and invertibility
(`AlgebraicGeometry.SimplicialScheme.pullHom'_hom_self_of_comp`).

## References

* [Stacks Project, Tag 07TH](https://stacks.math.columbia.edu/tag/07TH)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
* [Stacks Project, Tag 024A](https://stacks.math.columbia.edu/tag/024A)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace AlgebraicGeometry.SimplicialScheme

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-! ### Pairs on `(X/S)_•` and descent data relative to `{f}` -/

section Pair

open Pseudofunctor.LocallyDiscreteOpToCat Pseudofunctor.DescentData' Stacks.Groupoids


/-- The chosen fibre products of the one-element family `{f}`: the degree-one part `(X/S)_1`. -/
abbrev cechSq : ∀ i j : PUnit.{1}, ChosenPullback ((PreZeroHypercover.singleton.{0} f).f i)
    ((PreZeroHypercover.singleton.{0} f).f j) := fun _ _ => cechChosenPullback f

/-- The chosen triple fibre products of the one-element family `{f}`: the degree-two part
`(X/S)_2`. -/
abbrev cechSq₃ : ∀ i₁ i₂ i₃ : PUnit.{1},
    ChosenPullback₃ (cechSq f i₁ i₂) (cechSq f i₂ i₃) (cechSq f i₁ i₃) :=
  fun _ _ _ => cechChosenPullback₃ f

/-- Descent data relative to the one-element family `{f}`, presented over the chosen fibre
products `(X/S)_1` and `(X/S)_2`. -/
abbrev CechDescentData := modulePullbackPseudofunctor.DescentData' (cechSq f) (cechSq₃ f)

/-- The objects of `AlgebraicGeometry.SimplicialScheme.CechDescentData`: sheaves of modules on
the sole member `X` of the family, as the pullback pseudofunctor spells them. -/
abbrev CechObj := modulePullbackPseudofunctor.obj
  (.mk (op ((PreZeroHypercover.singleton.{0} f).X PUnit.unit)))

/-- The transitions of `AlgebraicGeometry.SimplicialScheme.CechDescentData`: morphisms
`pr_0^* M ⟶ pr_1^* N` on `(X/S)_1`. -/
abbrev CechHom (M N : CechObj f) :=
  (modulePullbackPseudofunctor.map (cechSq f PUnit.unit PUnit.unit).p₁.op.toLoc).toFunctor.obj M ⟶
    (modulePullbackPseudofunctor.map (cechSq f PUnit.unit PUnit.unit).p₂.op.toLoc).toFunctor.obj N

/-- The category of descent data relative to `{f}`. -/
instance : Category (CechDescentData f) := Pseudofunctor.DescentData'.instCategory

variable {f}

/-- An object of `CechObj f`, read as a sheaf of modules on `X`. -/
def toSchX (M : CechObj f) : X.Modules := M

/-- A sheaf of modules on `X`, read as an object of `CechObj f`. -/
def ofSchX (M : X.Modules) : CechObj f := M

/-- A morphism of `CechObj f`, read as a morphism of sheaves of modules on `X`. -/
def toSchXHom {M N : CechObj f} (φ : M ⟶ N) : toSchX M ⟶ toSchX N := φ

/-- A morphism of sheaves of modules on `X`, read as a morphism of `CechObj f`. -/
def ofSchXHom {M N : CechObj f} (φ : toSchX M ⟶ toSchX N) : M ⟶ N := φ

/-- A transition, read as a morphism `pr_0^* M ⟶ pr_1^* N` of sheaves of modules on `(X/S)_1`. -/
def schemeHomX {M N : CechObj f} (γ : CechHom f M N) :
    (Scheme.Modules.pullback (proj f 1 0)).obj (toSchX M) ⟶
      (Scheme.Modules.pullback (proj f 1 1)).obj (toSchX N) := γ

/-- A morphism `pr_0^* M ⟶ pr_1^* N` of sheaves of modules on `(X/S)_1`, read as a transition. -/
def ofSchemeHomX {M N : CechObj f}
    (γ : (Scheme.Modules.pullback (proj f 1 0)).obj (toSchX M) ⟶
      (Scheme.Modules.pullback (proj f 1 1)).obj (toSchX N)) : CechHom f M N := γ

/-- Reading a morphism `pr_0^* M ⟶ pr_1^* N` as a transition and back returns it unchanged. -/
@[simp] theorem schemeHomX_ofSchemeHomX {M N : CechObj f}
    (γ : (Scheme.Modules.pullback (proj f 1 0)).obj (toSchX M) ⟶
      (Scheme.Modules.pullback (proj f 1 1)).obj (toSchX N)) :
    schemeHomX (ofSchemeHomX γ) = γ := rfl

/-- Reading a morphism of sheaves of modules on `X` in `CechObj f` and back returns it
unchanged. -/
@[simp] theorem toSchXHom_ofSchXHom {M N : CechObj f} (φ : toSchX M ⟶ toSchX N) :
    toSchXHom (ofSchXHom φ) = φ := rfl

/-- `toSchXHom` sends the identity of `M` to the identity of `toSchX M`. -/
theorem toSchXHom_id (M : CechObj f) : toSchXHom (𝟙 M) = 𝟙 (toSchX M) := rfl

/-- `toSchXHom` sends a composite to the composite of the images. -/
theorem toSchXHom_comp {M N P : CechObj f} (φ : M ⟶ N) (ψ : N ⟶ P) :
    toSchXHom (φ ≫ ψ) = toSchXHom φ ≫ toSchXHom ψ := rfl

/-- Two morphisms of `CechObj f` are equal exactly when their images under `toSchXHom` are. -/
theorem toSchXHom_injective {M N : CechObj f} {φ ψ : M ⟶ N} :
    toSchXHom φ = toSchXHom ψ ↔ φ = ψ := Iff.rfl

/-- Two transitions are equal exactly when their images under `schemeHomX` are. -/
theorem schemeHomX_injective {M N : CechObj f} {γ γ' : CechHom f M N} :
    schemeHomX γ = schemeHomX γ' ↔ γ = γ' := Iff.rfl

/-- Pulling back a morphism and composing with a transition, in the two spellings. -/
theorem map_toSchXHom_comp_schemeHomX {M M' N : CechObj f} (φ : M ⟶ M') (γ : CechHom f M' N) :
    (Scheme.Modules.pullback (proj f 1 0)).map (toSchXHom φ) ≫ schemeHomX γ =
      schemeHomX ((modulePullbackPseudofunctor.map
        (cechSq f PUnit.unit PUnit.unit).p₁.op.toLoc).toFunctor.map φ ≫ γ) := rfl

/-- Composing a transition with a pulled back morphism, in the two spellings. -/
theorem schemeHomX_comp_map_toSchXHom {M N N' : CechObj f} (γ : CechHom f M N) (φ : N ⟶ N') :
    schemeHomX γ ≫ (Scheme.Modules.pullback (proj f 1 1)).map (toSchXHom φ) =
      schemeHomX (γ ≫ (modulePullbackPseudofunctor.map
        (cechSq f PUnit.unit PUnit.unit).p₂.op.toLoc).toFunctor.map φ) := rfl

/-- `schemeHomX` of an isomorphism is an isomorphism. -/
instance isIso_schemeHomX {M N : CechObj f} (γ : CechHom f M N) [IsIso γ] :
    IsIso (schemeHomX γ) :=
  isIso_schemeHom γ

/-- The transitions of a descent datum relative to `{f}` are isomorphisms. -/
instance CechDescentData.isIso_hom (D : CechDescentData f) (i j : PUnit.{1}) :
    IsIso (D.hom i j) := by
  have e : pullHom' D.hom (cechSq f i j).p (cechSq f i j).p₁ (cechSq f i j).p₂
      (cechSq f i j).hp₁ (cechSq f i j).hp₂ = D.hom i j := pullHom'_p₁_p₂ D.hom i j
  rw [← e]
  refine ⟨pullHom' D.hom (cechSq f i j).p (cechSq f i j).p₂ (cechSq f i j).p₁
    (cechSq f i j).hp₂ (cechSq f i j).hp₁, ?_, ?_⟩ <;> rw [D.comp_pullHom', D.pullHom'_self]

/-- The isomorphism `d¹_1^* pr^* M ≅ d¹_0^* pr^* M` on `(X/S)_1` transported from an isomorphism
`γ : pr_0^* M ≅ pr_1^* M`, where `pr : (X/S)_0 ⟶ X` is the vertex. -/
def cechIso {M : CechObj f} (γ : CechHom f M M) [IsIso γ] :
    ((zariskiModuleFamily (simplicialScheme f)).map (SimplexCategory.δ (1 : Fin 2))).obj
        ((Scheme.Modules.pullback (proj f 0 0)).obj (toSchX M)) ≅
      ((zariskiModuleFamily (simplicialScheme f)).map (SimplexCategory.δ (0 : Fin 2))).obj
        ((Scheme.Modules.pullback (proj f 0 0)).obj (toSchX M)) :=
  asIso (cechTransport (schemeHomX γ))

/-- The forward morphism of `cechIso γ` is the transport of `schemeHomX γ`. -/
theorem cechIso_hom {M : CechObj f} (γ : CechHom f M M) [IsIso γ] :
    (cechIso γ).hom = cechTransport (schemeHomX γ) := rfl

/-- **The cocycle condition of descent data relative to `{f}` is the cocycle condition of the
transported pair on `(X/S)_•`.** -/
theorem pullHom_cocycle_iff_isCocycle (M : CechObj f) (γ : CechHom f M M) [IsIso γ] :
    pullHom γ (cechSq₃ f PUnit.unit PUnit.unit PUnit.unit).p₁₂
        (cechSq₃ f PUnit.unit PUnit.unit PUnit.unit).p₁
        (cechSq₃ f PUnit.unit PUnit.unit PUnit.unit).p₂
        (ChosenPullback₃.p₁₂_p₁ _) (ChosenPullback₃.p₁₂_p₂ _) ≫
      pullHom γ (cechSq₃ f PUnit.unit PUnit.unit PUnit.unit).p₂₃
        (cechSq₃ f PUnit.unit PUnit.unit PUnit.unit).p₂
        (cechSq₃ f PUnit.unit PUnit.unit PUnit.unit).p₃
        (ChosenPullback₃.p₂₃_p₂ _) (ChosenPullback₃.p₂₃_p₃ _) =
      pullHom γ (cechSq₃ f PUnit.unit PUnit.unit PUnit.unit).p₁₃
        (cechSq₃ f PUnit.unit PUnit.unit PUnit.unit).p₁
        (cechSq₃ f PUnit.unit PUnit.unit PUnit.unit).p₃
        (ChosenPullback₃.p₁₃_p₁ _) (ChosenPullback₃.p₁₃_p₃ _) ↔
    (zariskiModuleFamily (simplicialScheme f)).IsCocycle
      ((Scheme.Modules.pullback (proj f 0 0)).obj (toSchX M)) (cechIso γ) := by
  rw [pullHom_comp_iff_reindexCocycle]
  exact (isCocycle_cechTransport_iff_reindexCocycle (schemeHomX γ)).symm

/-- The vertex `(X/S)_0 ⟶ X` is an isomorphism. -/
instance isIso_proj_zero_zero : IsIso (proj f 0 0) :=
  ⟨⟨vertexSimplex f (𝟙 X), zero_hom_ext f (by simp), by simp⟩⟩

/-- **The pair on `(X/S)_•` of a descent datum relative to `{f}`**: the pullback `pr^* F` of its
module to `(X/S)_0` along the vertex `pr`, with its transition transported to the two faces
`(X/S)_1 ⟶ (X/S)_0`. -/
def CechDescentData.toPair (D : CechDescentData f) :
    (zariskiModuleFamily (simplicialScheme f)).Pair where
  obj := (Scheme.Modules.pullback (proj f 0 0)).obj (toSchX (D.obj PUnit.unit))
  iso := cechIso (D.hom PUnit.unit PUnit.unit)
  cocycle := (pullHom_cocycle_iff_isCocycle (D.obj PUnit.unit) (D.hom PUnit.unit PUnit.unit)).1
    (D.pullHom_comp_eq PUnit.unit)

/-- The module of the pair of `D` is the pullback of the module of `D` along the vertex. -/
theorem CechDescentData.toPair_obj (D : CechDescentData f) :
    D.toPair.obj = (Scheme.Modules.pullback (proj f 0 0)).obj (toSchX (D.obj PUnit.unit)) := rfl

/-- The isomorphism of the pair of `D` is the transport of the transition of `D`. -/
theorem CechDescentData.toPair_iso (D : CechDescentData f) :
    D.toPair.iso = cechIso (D.hom PUnit.unit PUnit.unit) := rfl

/-- A morphism of the modules commutes with the transported isomorphisms exactly when it commutes
with the transitions. -/
theorem cechIso_comm_iff {M₁ M₂ : CechObj f} (γ₁ : CechHom f M₁ M₁) (γ₂ : CechHom f M₂ M₂)
    [IsIso γ₁] [IsIso γ₂] (φ : M₁ ⟶ M₂) :
    ((zariskiModuleFamily (simplicialScheme f)).map (SimplexCategory.δ (1 : Fin 2))).map
          ((Scheme.Modules.pullback (proj f 0 0)).map (toSchXHom φ)) ≫ (cechIso γ₂).hom =
        (cechIso γ₁).hom ≫
          ((zariskiModuleFamily (simplicialScheme f)).map (SimplexCategory.δ (0 : Fin 2))).map
            ((Scheme.Modules.pullback (proj f 0 0)).map (toSchXHom φ)) ↔
      (modulePullbackPseudofunctor.map (cechSq f PUnit.unit PUnit.unit).p₁.op.toLoc).toFunctor.map
          φ ≫ γ₂ =
        γ₁ ≫ (modulePullbackPseudofunctor.map
          (cechSq f PUnit.unit PUnit.unit).p₂.op.toLoc).toFunctor.map φ := by
  rw [cechIso_hom, cechIso_hom]
  show (Scheme.Modules.pullback ((simplicialScheme f).map (SimplexCategory.δ (1 : Fin 2)).op)).map
      ((Scheme.Modules.pullback (proj f 0 0)).map (toSchXHom φ)) ≫ cechTransport (schemeHomX γ₂) =
    cechTransport (schemeHomX γ₁) ≫
      (Scheme.Modules.pullback ((simplicialScheme f).map (SimplexCategory.δ (0 : Fin 2)).op)).map
        ((Scheme.Modules.pullback (proj f 0 0)).map (toSchXHom φ)) ↔ _
  rw [← map_comp_transportHom, ← transportHom_comp_map, map_toSchXHom_comp_schemeHomX,
    schemeHomX_comp_map_toSchXHom, ← schemeHomX_injective]
  exact ⟨fun h => transportHom_injective _ _ h, fun h => by rw [h]⟩

/-- The morphism of pairs of a morphism of descent data. -/
def CechDescentData.toPairMap {D₁ D₂ : CechDescentData f} (φ : D₁ ⟶ D₂) :
    D₁.toPair ⟶ D₂.toPair where
  map := (Scheme.Modules.pullback (proj f 0 0)).map (toSchXHom (φ.hom PUnit.unit))
  comm := (cechIso_comm_iff _ _ (φ.hom PUnit.unit)).2 (φ.comm PUnit.unit PUnit.unit)

/-- The morphism of modules underlying `CechDescentData.toPairMap φ` is the pullback of `φ`
along the vertex. -/
theorem CechDescentData.toPairMap_map {D₁ D₂ : CechDescentData f} (φ : D₁ ⟶ D₂) :
    (CechDescentData.toPairMap φ).map =
      (Scheme.Modules.pullback (proj f 0 0)).map (toSchXHom (φ.hom PUnit.unit)) := rfl

variable (f) in
/-- **The functor from descent data relative to `{f}` to pairs on `(X/S)_•`.** -/
def cechDescentDataToPair :
    CechDescentData f ⥤ (zariskiModuleFamily (simplicialScheme f)).Pair where
  obj D := D.toPair
  map φ := CechDescentData.toPairMap φ
  map_id D := SimplicialPseudoFamily.Pair.hom_ext (by
    rw [CechDescentData.toPairMap_map]
    exact (congrArg (Scheme.Modules.pullback (proj f 0 0)).map (toSchXHom_id _)).trans
      ((Scheme.Modules.pullback (proj f 0 0)).map_id _))
  map_comp φ ψ := SimplicialPseudoFamily.Pair.hom_ext (by
    rw [CechDescentData.toPairMap_map]
    exact (congrArg (Scheme.Modules.pullback (proj f 0 0)).map (toSchXHom_comp _ _)).trans
      ((Scheme.Modules.pullback (proj f 0 0)).map_comp _ _))

/-- The functor `cechDescentDataToPair f` is faithful. -/
instance : (cechDescentDataToPair f).Faithful where
  map_injective {D₁ D₂} {φ ψ} h := by
    ext i
    cases i
    have h' : (Scheme.Modules.pullback (proj f 0 0)).map (toSchXHom (φ.hom PUnit.unit)) =
        (Scheme.Modules.pullback (proj f 0 0)).map (toSchXHom (ψ.hom PUnit.unit)) :=
      congrArg SimplicialPseudoFamily.Pair.Hom.map h
    exact toSchXHom_injective.1 ((Scheme.Modules.pullback (proj f 0 0)).map_injective h')

/-- The functor `cechDescentDataToPair f` is full. -/
instance : (cechDescentDataToPair f).Full where
  map_surjective {D₁ D₂} g := by
    let g₀ : (Scheme.Modules.pullback (proj f 0 0)).obj (toSchX (D₁.obj PUnit.unit)) ⟶
        (Scheme.Modules.pullback (proj f 0 0)).obj (toSchX (D₂.obj PUnit.unit)) := g.map
    let φ₀ := (Scheme.Modules.pullback (proj f 0 0)).preimage g₀
    have hφ₀ : (Scheme.Modules.pullback (proj f 0 0)).map (toSchXHom (ofSchXHom φ₀)) = g₀ := by
      rw [toSchXHom_ofSchXHom, Functor.map_preimage]
    refine ⟨{ hom := fun _ => ofSchXHom φ₀, comm := ?_ }, ?_⟩
    · rintro ⟨⟩ ⟨⟩
      refine (cechIso_comm_iff (D₁.hom PUnit.unit PUnit.unit) (D₂.hom PUnit.unit PUnit.unit)
        (ofSchXHom φ₀)).1 ?_
      rw [hφ₀]
      exact g.comm
    · exact SimplicialPseudoFamily.Pair.hom_ext hφ₀

section EssSurj

variable (A : (zariskiModuleFamily (simplicialScheme f)).Pair)

/-- The module on `X` of a pair on `(X/S)_•`: the pullback of its module along the inverse of the
vertex `(X/S)_0 ⟶ X`. -/
def pairModule : CechObj f := ofSchX ((Scheme.Modules.pullback (inv (proj f 0 0))).obj A.obj)

/-- The pullback of `pairModule A` to `(X/S)_0` is the module of the pair. -/
def pairModuleIso :
    (Scheme.Modules.pullback (proj f 0 0)).obj (toSchX (pairModule A)) ≅ A.obj :=
  pullbackPasteOfEq (proj f 0 0) (inv (proj f 0 0)) (𝟙 _) (IsIso.hom_inv_id _) A.obj ≪≫
    (Scheme.Modules.pullbackId _).app A.obj

/-- The isomorphism of the pair, conjugated to the pullback of `pairModule A`. -/
def pairConjIso :
    ((zariskiModuleFamily (simplicialScheme f)).map (SimplexCategory.δ (1 : Fin 2))).obj
        ((Scheme.Modules.pullback (proj f 0 0)).obj (toSchX (pairModule A))) ≅
      ((zariskiModuleFamily (simplicialScheme f)).map (SimplexCategory.δ (0 : Fin 2))).obj
        ((Scheme.Modules.pullback (proj f 0 0)).obj (toSchX (pairModule A))) :=
  ((zariskiModuleFamily (simplicialScheme f)).map (SimplexCategory.δ (1 : Fin 2))).mapIso
      (pairModuleIso A) ≪≫ A.iso ≪≫
    ((zariskiModuleFamily (simplicialScheme f)).map (SimplexCategory.δ (0 : Fin 2))).mapIso
      (pairModuleIso A).symm

/-- The conjugated isomorphism `pairConjIso A` satisfies the cocycle condition. -/
theorem isCocycle_pairConjIso :
    (zariskiModuleFamily (simplicialScheme f)).IsCocycle
      ((Scheme.Modules.pullback (proj f 0 0)).obj (toSchX (pairModule A))) (pairConjIso A) := by
  unfold pairConjIso
  exact SimplicialPseudoFamily.isCocycle_conj (P := zariskiModuleFamily (simplicialScheme f))
    (pairModuleIso A) A.cocycle

/-- The transition of the descent datum of a pair. -/
def pairHom : CechHom f (pairModule A) (pairModule A) :=
  ofSchemeHomX (transportPreimage (delta_one_proj_zero_id f) (delta_zero_proj_zero_id f)
    (pairConjIso A).hom)

/-- The transport of the transition `pairHom A` is the forward morphism of `pairConjIso A`. -/
theorem cechTransport_pairHom :
    cechTransport (schemeHomX (pairHom A)) = (pairConjIso A).hom :=
  transportHom_transportPreimage _ _ _

/-- The transition `pairHom A` is an isomorphism. -/
instance isIso_pairHom : IsIso (pairHom A) := by
  have : IsIso (cechTransport (schemeHomX (pairHom A))) := by
    rw [cechTransport_pairHom]
    infer_instance
  have : IsIso (schemeHomX (pairHom A)) :=
    isIso_of_isIso_transportHom (delta_one_proj_zero_id f) (delta_zero_proj_zero_id f) _
  exact this

/-- The isomorphism transported from `pairHom A` is `pairConjIso A`. -/
theorem cechIso_pairHom : cechIso (pairHom A) = pairConjIso A :=
  Iso.ext (cechTransport_pairHom A)

/-- The transition `pairHom A` satisfies the cocycle condition on `(X/S)_2`. -/
theorem pairHom_cocycle :
    pullHom (pairHom A) (cechSq₃ f PUnit.unit PUnit.unit PUnit.unit).p₁₂
        (cechSq₃ f PUnit.unit PUnit.unit PUnit.unit).p₁
        (cechSq₃ f PUnit.unit PUnit.unit PUnit.unit).p₂
        (ChosenPullback₃.p₁₂_p₁ _) (ChosenPullback₃.p₁₂_p₂ _) ≫
      pullHom (pairHom A) (cechSq₃ f PUnit.unit PUnit.unit PUnit.unit).p₂₃
        (cechSq₃ f PUnit.unit PUnit.unit PUnit.unit).p₂
        (cechSq₃ f PUnit.unit PUnit.unit PUnit.unit).p₃
        (ChosenPullback₃.p₂₃_p₂ _) (ChosenPullback₃.p₂₃_p₃ _) =
      pullHom (pairHom A) (cechSq₃ f PUnit.unit PUnit.unit PUnit.unit).p₁₃
        (cechSq₃ f PUnit.unit PUnit.unit PUnit.unit).p₁
        (cechSq₃ f PUnit.unit PUnit.unit PUnit.unit).p₃
        (ChosenPullback₃.p₁₃_p₁ _) (ChosenPullback₃.p₁₃_p₃ _) := by
  refine (pullHom_cocycle_iff_isCocycle (pairModule A) (pairHom A)).2 ?_
  rw [cechIso_pairHom]
  exact isCocycle_pairConjIso A

/-- **The descent datum relative to `{f}` of a pair on `(X/S)_•`.** -/
def pairDescentData : CechDescentData f :=
  descentData'OfPUnit modulePullbackPseudofunctor (cechSq f) (cechSq₃ f)
    (pairModule A) (pairHom A) (pairHom_cocycle A)

/-- A conjugation identity for two functors and an isomorphism. -/
theorem map_hom_comp_eq_conj {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (G₁ G₂ : 𝒞 ⥤ 𝒟) {x y : 𝒞}
    (c : x ≅ y) (a : G₁.obj y ⟶ G₂.obj y) :
    G₁.map c.hom ≫ a = (G₁.map c.hom ≫ a ≫ G₂.map c.inv) ≫ G₂.map c.hom := by
  simp

/-- The pair of the descent datum of a pair is the pair. -/
def pairDescentDataToPairIso : (pairDescentData A).toPair ≅ A :=
  SimplicialPseudoFamily.Pair.isoMk (pairModuleIso A) (by
    change _ = (cechIso (pairHom A)).hom ≫ _
    rw [cechIso_pairHom]
    exact map_hom_comp_eq_conj _ _ (pairModuleIso A) A.iso.hom)

end EssSurj

/-- The functor `cechDescentDataToPair f` is essentially surjective. -/
instance : (cechDescentDataToPair f).EssSurj where
  mem_essImage A := ⟨pairDescentData A, ⟨pairDescentDataToPairIso A⟩⟩

/-- The functor `cechDescentDataToPair f` is an equivalence. -/
instance : (cechDescentDataToPair f).IsEquivalence where

variable (f) in
/-- Descent data over the chosen fibre products `(X/S)_1`, `(X/S)_2` are descent data relative
to `{f}`. -/
def cechDescentDataEquiv :
    CechDescentData f ≌
      modulePullbackPseudofunctor.DescentData (PreZeroHypercover.singleton.{0} f).f :=
  Pseudofunctor.DescentData'.descentDataEquivalence modulePullbackPseudofunctor
    (cechSq f) (cechSq₃ f)

variable (f) in
/-- **Descent data relative to `{f}` are pairs on `(X/S)_•`** (Stacks 07TH for the simplicial
scheme of Stacks 024A, read against descent data). -/
def descentDataEquivPair :
    modulePullbackPseudofunctor.DescentData (PreZeroHypercover.singleton.{0} f).f ≌
      (zariskiModuleFamily (simplicialScheme f)).Pair :=
  (cechDescentDataEquiv f).symm.trans (cechDescentDataToPair f).asEquivalence

/-- A sheaf of modules on `X` is quasi-coherent exactly when its pullback to `(X/S)_0` is. -/
theorem isQuasicoherent_iff_pullback_proj (M : X.Modules) :
    M.IsQuasicoherent ↔ ((Scheme.Modules.pullback (proj f 0 0)).obj M).IsQuasicoherent := by
  refine ⟨fun _ => Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _,
    fun h => ?_⟩
  have e : (Scheme.Modules.pullback (inv (proj f 0 0))).obj
      ((Scheme.Modules.pullback (proj f 0 0)).obj M) ≅ M :=
    pullbackPasteOfEq (inv (proj f 0 0)) (proj f 0 0) (𝟙 _) (IsIso.inv_hom_id _) M ≪≫
      (Scheme.Modules.pullbackId _).app M
  exact (SheafOfModules.isQuasicoherent _).prop_of_iso e
    (Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _)

variable (f) in
/-- The functor from quasi-coherent descent data relative to `{f}` to the pairs on `(X/S)_•`
with quasi-coherent module. -/
def quasicoherentDescentDataToPair :
    QuasicoherentDescentData (PreZeroHypercover.singleton.{0} f).f ⥤
      QuasicoherentZariskiPair (simplicialScheme f) :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ (descentDataEquivPair f).functor)
    (fun D => (isQuasicoherent_iff_pullback_proj (toSchX (D.obj.obj PUnit.unit))).1
      (D.property PUnit.unit))

/-- The functor `quasicoherentDescentDataToPair f` is faithful. -/
instance : (quasicoherentDescentDataToPair f).Faithful :=
  have : (quasicoherentDescentDataToPair f ⋙ ObjectProperty.ι _).Faithful :=
    (inferInstance : (ObjectProperty.ι _ ⋙ (descentDataEquivPair f).functor).Faithful)
  Functor.Faithful.of_comp _ (ObjectProperty.ι _)

/-- The functor `quasicoherentDescentDataToPair f` is full. -/
instance : (quasicoherentDescentDataToPair f).Full :=
  have : (quasicoherentDescentDataToPair f ⋙ ObjectProperty.ι _).Full :=
    (inferInstance : (ObjectProperty.ι _ ⋙ (descentDataEquivPair f).functor).Full)
  Functor.Full.of_comp_faithful _ (ObjectProperty.ι _)

/-- The functor `quasicoherentDescentDataToPair f` is essentially surjective. -/
instance : (quasicoherentDescentDataToPair f).EssSurj where
  mem_essImage A := by
    let D := (descentDataEquivPair f).inverse.obj A.obj
    let e : (descentDataEquivPair f).functor.obj D ≅ A.obj :=
      (descentDataEquivPair f).counitIso.app A.obj
    have h0 :
        ((Scheme.Modules.pullback (proj f 0 0)).obj (toSchX (D.obj PUnit.unit))).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent _).prop_of_iso
        (SimplicialPseudoFamily.Pair.objIso e.symm) A.property
    exact ⟨⟨D, fun ⟨⟩ => (isQuasicoherent_iff_pullback_proj (toSchX (D.obj PUnit.unit))).2 h0⟩,
      ⟨ObjectProperty.isoMk _ e⟩⟩

/-- The functor `quasicoherentDescentDataToPair f` is an equivalence. -/
instance : (quasicoherentDescentDataToPair f).IsEquivalence where

variable (f) in
/-- **Quasi-coherent descent data relative to `{f}` are the pairs on `(X/S)_•` with
quasi-coherent module.** -/
def quasicoherentDescentDataEquivPair :
    QuasicoherentDescentData (PreZeroHypercover.singleton.{0} f).f ≌
      QuasicoherentZariskiPair (simplicialScheme f) :=
  (quasicoherentDescentDataToPair f).asEquivalence

variable (f) in
/-- **Quasi-coherent descent data relative to `{f}` are the quasi-coherent modules on the total
Zariski site of `(X/S)_•`** (Stacks 07TH and Stacks 0D7M for the simplicial scheme of
Stacks 024A). -/
def quasicoherentDescentDataEquivZariski :
    QuasicoherentDescentData (PreZeroHypercover.singleton.{0} f).f ≌
      QuasicoherentZariskiModule (simplicialScheme f) :=
  (quasicoherentDescentDataEquivPair f).trans
    (quasicoherentEquivQuasicoherentPair (simplicialScheme f)).symm

end Pair

end AlgebraicGeometry.SimplicialScheme
