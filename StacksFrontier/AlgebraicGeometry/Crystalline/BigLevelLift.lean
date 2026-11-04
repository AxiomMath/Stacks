module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigLevelBase
public import StacksFrontier.AlgebraicGeometry.Crystalline.ChangeBaseBigCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Functoriality

/-!
# The big crystalline sites of the finite levels inside `CRIS(X/S)`

Let `X/S` be a global crystalline situation with affine base and let `S_e ⊂ S` be its finite
divided power levels. Change of divided power base along `S_e ⟶ S` and `𝟙 X` is a functor
`u_e : CRIS(X/S_e) ⥤ CRIS(X/S)`, and:

* `u_e` is fully faithful, because `S_e ⟶ S` is a monomorphism;
* `u_e` is *sieve-like*: an object of `CRIS(X/S)` mapping to an object in the image of `u_e` is in
  the image of `u_e`, canonically, and more generally an object `(U, T, δ)` of `CRIS(X/S)` lies in
  the image as soon as `p^e` vanishes on `Γ(T, 𝒪_T)`;
* consequently every slice functor `CRIS(X/S_e)/W ⥤ CRIS(X/S)/u_e(W)` is an equivalence.

It also records that change of divided power base on the big crystalline sites composes up to the
canonical isomorphism carried by the identity of the underlying thickening, and the same for the
pullbacks of sheaves of modules.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.changeBaseCompIso` — change of base composes.
* `Crystalline.GlobalCrystallineSituation.changeBaseBigModulePullbackCompIso` — the pullbacks of
  sheaves of modules compose.
* `Crystalline.GlobalCrystallineSituation.levelChangeBase` — the functor `u_e`.
* `Crystalline.GlobalCrystallineSituation.Thickening.levelLiftVia` and
  `Crystalline.GlobalCrystallineSituation.Thickening.levelLiftViaIso` — an object of `CRIS(X/S)`
  whose structure morphism factors through `S_e` is the image of an object of `CRIS(X/S_e)`.

## Main results

* `Crystalline.GlobalCrystallineSituation.levelChangeBaseFullyFaithful` — `u_e` is fully
  faithful.
* `Crystalline.GlobalCrystallineSituation.isEquivalence_overPost_levelChangeBase` — the slice
  functors of `u_e` are equivalences.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation

open DividedPowerScheme

/-! ### Composition of changes of base on the big site -/

section Composition

variable (S S' S'' : GlobalCrystallineSituation.{u})
  (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
  (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
  (f' : S'.S ⟶ S''.S) (g' : S'.X ⟶ S''.X)
  (h' : S'.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f' = g' ≫ S''.toClosedFiber)
  {f'' : S.S ⟶ S''.S} {g'' : S.X ⟶ S''.X}
  (h'' : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f'' = g'' ≫ S''.toClosedFiber)
  (hf : f ≫ f' = f'') (hg : g ≫ g' = g'')

/-- **Change of divided power base on the big crystalline sites composes**, up to the natural
isomorphism whose components are the identity of the underlying thickening: changing base twice
reassociates the structure morphisms `(T ⟶ S ⟶ S') ⟶ S''` against `T ⟶ S ⟶ S''`. -/
def changeBaseCompIso :
    changeBase S S' f g h ⋙ changeBase S' S'' f' g' h' ≅ changeBase S S'' f'' g'' h'' :=
  NatIso.ofComponents
    (fun B =>
      { hom :=
          { sourceHom := 𝟙 _
            targetHom := 𝟙 _
            immersion_naturality := by simp
            base_naturality := by
              change 𝟙 _ ≫ B.toBase ≫ f'' = (B.toBase ≫ f) ≫ f'
              rw [Category.id_comp, Category.assoc, hf]
            toX_naturality := by
              change 𝟙 _ ≫ B.toX ≫ g'' = (B.toX ≫ g) ≫ g'
              rw [Category.id_comp, Category.assoc, hg] }
        inv :=
          { sourceHom := 𝟙 _
            targetHom := 𝟙 _
            immersion_naturality := by simp
            base_naturality := by
              change 𝟙 _ ≫ (B.toBase ≫ f) ≫ f' = B.toBase ≫ f''
              rw [Category.id_comp, Category.assoc, hf]
            toX_naturality := by
              change 𝟙 _ ≫ (B.toX ≫ g) ≫ g' = B.toX ≫ g''
              rw [Category.id_comp, Category.assoc, hg] }
        hom_inv_id := by apply Thickening.Hom.ext <;> exact Category.comp_id _
        inv_hom_id := by apply Thickening.Hom.ext <;> exact Category.comp_id _ })
    (fun k => by
      apply Thickening.Hom.ext <;> exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The comparison of two changes of base is the identity on thickened schemes. -/
@[simp]
theorem changeBaseCompIso_hom_app_sourceHom (B : Thickening S) :
    ((changeBaseCompIso S S' S'' f g h f' g' h' h'' hf hg).hom.app B).sourceHom = 𝟙 _ := rfl

/-- The comparison of two changes of base is the identity on ambient schemes. -/
@[simp]
theorem changeBaseCompIso_hom_app_targetHom (B : Thickening S) :
    ((changeBaseCompIso S S' S'' f g h f' g' h' h'' hf hg).hom.app B).targetHom = 𝟙 _ := rfl

/-- The inverse comparison is the identity on thickened schemes. -/
@[simp]
theorem changeBaseCompIso_inv_app_sourceHom (B : Thickening S) :
    ((changeBaseCompIso S S' S'' f g h f' g' h' h'' hf hg).inv.app B).sourceHom = 𝟙 _ := rfl

/-- The inverse comparison is the identity on ambient schemes. -/
@[simp]
theorem changeBaseCompIso_inv_app_targetHom (B : Thickening S) :
    ((changeBaseCompIso S S' S'' f g h f' g' h' h'' hf hg).inv.app B).targetHom = 𝟙 _ := rfl

/-- **The pullbacks of sheaves of modules along two changes of divided power base compose** to the
pullback along the composite: restricting along `changeBase S' S''` and then along
`changeBase S S'` is restricting along their composite, which is `changeBase S S''` up to
`changeBaseCompIso`; the comparisons of structure sheaves are identities throughout. -/
def changeBaseBigModulePullbackCompIso :
    changeBaseBigModulePullback S' S'' f' g' h' ⋙ changeBaseBigModulePullback S S' f g h ≅
      changeBaseBigModulePullback S S'' f'' g'' h'' :=
  haveI : (changeBase S S' f g h ⋙ changeBase S' S'' f' g' h').IsContinuous (topology S)
      (topology S'') := Functor.isContinuous_comp _ _ _ (topology S') _
  SheafOfModules.pushforwardComp (F := changeBase S S' f g h) (G := changeBase S' S'' f' g' h')
      (changeBaseStructureHom S S' f g h) (changeBaseStructureHom S' S'' f' g' h') ≪≫
    SheafOfModules.pushforwardCongr₂
      (e := (changeBaseCompIso S S' S'' f g h f' g' h' h'' hf hg).symm)
      (ψ := changeBaseStructureHom S S'' f'' g'' h'') (he := by ext; rfl)

end Composition

/-! ### The levels of an affine base -/

section Level

variable (S : GlobalCrystallineSituation.{u}) [IsAffine S.S.scheme]

/-- The underlying morphism of schemes of `S_e ⟶ S` is a monomorphism: it is a closed immersion
followed by an isomorphism. -/
instance mono_levelProj_hom {e : ℕ} (he : S.IsLevel e) : Mono (S.levelProj he).hom := by
  change Mono ((pAdicLevelSchemeProj S.baseIdeal S.baseDividedPowers S.p he).hom ≫
    (S.baseSpecIso.hom).hom)
  have : IsIso (S.baseSpecIso.hom).hom := by
    change IsIso (specIsoOfIsAffineHom S.S).hom
    exact inferInstanceAs (IsIso S.S.scheme.isoSpec.inv)
  infer_instance

/-- `S_e ⟶ S` is a monomorphism of divided power schemes. -/
instance mono_levelProj {e : ℕ} (he : S.IsLevel e) : Mono (S.levelProj he) :=
  mono_of_mono_hom inferInstance

/-- **The functor `u_e : CRIS(X/S_e) ⥤ CRIS(X/S)`**, change of divided power base along `S_e ⟶ S`
and the identity of `X`. -/
abbrev levelChangeBase {e : ℕ} (he : S.IsLevel e) :
    Thickening (S.levelSituation he) ⥤ Thickening S :=
  changeBase (S.levelSituation he) S (S.levelProj he) (𝟙 S.X) (S.levelProj_condition he)

/-- **The transition functor `CRIS(X/S_m) ⥤ CRIS(X/S_e)`**, for `m ≤ e`. -/
abbrev levelStepChangeBase {m e : ℕ} (hm : S.IsLevel m) (he : S.IsLevel e) (hme : m ≤ e) :
    Thickening (S.levelSituation hm) ⥤ Thickening (S.levelSituation he) :=
  changeBase (S.levelSituation hm) (S.levelSituation he) (S.levelTransition hm he hme) (𝟙 S.X)
    (S.levelTransition_condition hm he hme)

/-- **The restriction `N ↦ N_e`** of sheaves of `𝒪_{X/S}`-modules on `CRIS(X/S)` to `CRIS(X/S_e)`,
the pullback along `u_e`. -/
abbrev levelPullback {e : ℕ} (he : S.IsLevel e) :
    SmallSite.BigModuleSheaf S ⥤ SmallSite.BigModuleSheaf (S.levelSituation he) :=
  changeBaseBigModulePullback (S.levelSituation he) S (S.levelProj he) (𝟙 S.X)
    (S.levelProj_condition he)

/-- The restriction of sheaves of modules from `CRIS(X/S_e)` to `CRIS(X/S_m)`, for `m ≤ e`. -/
abbrev levelStepPullback {m e : ℕ} (hm : S.IsLevel m) (he : S.IsLevel e) (hme : m ≤ e) :
    SmallSite.BigModuleSheaf (S.levelSituation he) ⥤
      SmallSite.BigModuleSheaf (S.levelSituation hm) :=
  changeBaseBigModulePullback (S.levelSituation hm) (S.levelSituation he)
    (S.levelTransition hm he hme) (𝟙 S.X) (S.levelTransition_condition hm he hme)

/-- **Restricting to `CRIS(X/S_e)` and then to `CRIS(X/S_m)` is restricting to `CRIS(X/S_m)`.** -/
def levelPullbackCompIso {m e : ℕ} (hm : S.IsLevel m) (he : S.IsLevel e) (hme : m ≤ e) :
    S.levelPullback he ⋙ S.levelStepPullback hm he hme ≅ S.levelPullback hm :=
  changeBaseBigModulePullbackCompIso _ _ _ _ _ _ _ _ _ (S.levelProj_condition hm)
    (S.levelTransition_comp_levelProj hm he hme) (Category.comp_id _)

/-- **An object of `CRIS(X/S)` whose structure morphism factors through `S_e` is an object of
`CRIS(X/S_e)`**: the same thickening, with the factorization as structure morphism. -/
def Thickening.levelLiftVia {e : ℕ} (he : S.IsLevel e) (V : Thickening S)
    (φ : V.thickening.target ⟶ (S.levelSituation he).S) (hφ : φ ≫ S.levelProj he = V.toBase) :
    Thickening (S.levelSituation he) where
  thickening := V.thickening
  toBase := φ
  toX := V.toX
  over_base := by
    rw [← cancel_mono (S.levelProj he).hom, Category.assoc, ← DividedPowerScheme.Hom.comp_hom,
      hφ, V.over_base, sourceToBase, sourceToBase, Category.assoc, Category.assoc,
      ← closedFiberMap_comp_closedFiberι (S.levelProj he),
      ← Category.assoc ((S.levelSituation he).toClosedFiber), S.levelProj_condition he,
      Category.id_comp]

/-- The lift to `CRIS(X/S_e)` has the same underlying thickening. -/
@[simp]
theorem Thickening.levelLiftVia_thickening {e : ℕ} (he : S.IsLevel e) (V : Thickening S)
    (φ : V.thickening.target ⟶ (S.levelSituation he).S) (hφ : φ ≫ S.levelProj he = V.toBase) :
    (V.levelLiftVia S he φ hφ).thickening = V.thickening := rfl

/-- The structure morphism of the lift is the given factorization through `S_e`. -/
@[simp]
theorem Thickening.levelLiftVia_toBase {e : ℕ} (he : S.IsLevel e) (V : Thickening S)
    (φ : V.thickening.target ⟶ (S.levelSituation he).S) (hφ : φ ≫ S.levelProj he = V.toBase) :
    (V.levelLiftVia S he φ hφ).toBase = φ := rfl

/-- **The image under `u_e` of the lift of an object is the object**, through the identity of the
underlying thickening. -/
def Thickening.levelLiftViaIso {e : ℕ} (he : S.IsLevel e) (V : Thickening S)
    (φ : V.thickening.target ⟶ (S.levelSituation he).S) (hφ : φ ≫ S.levelProj he = V.toBase) :
    (S.levelChangeBase he).obj (V.levelLiftVia S he φ hφ) ≅ V where
  hom :=
    { sourceHom := 𝟙 _
      targetHom := 𝟙 _
      immersion_naturality := by simp
      base_naturality := (Category.id_comp _).trans hφ.symm
      toX_naturality := (Category.id_comp _).trans (Category.comp_id _).symm }
  inv :=
    { sourceHom := 𝟙 _
      targetHom := 𝟙 _
      immersion_naturality := by simp
      base_naturality := (Category.id_comp _).trans hφ
      toX_naturality := (Category.id_comp _).trans (Category.comp_id _) }
  hom_inv_id := by apply Thickening.Hom.ext <;> exact Category.comp_id _
  inv_hom_id := by apply Thickening.Hom.ext <;> exact Category.comp_id _

/-- The identification of the image of the lift is the identity on thickened schemes. -/
@[simp]
theorem Thickening.levelLiftViaIso_hom_sourceHom {e : ℕ} (he : S.IsLevel e) (V : Thickening S)
    (φ : V.thickening.target ⟶ (S.levelSituation he).S) (hφ : φ ≫ S.levelProj he = V.toBase) :
    (V.levelLiftViaIso S he φ hφ).hom.sourceHom = 𝟙 _ := rfl

/-- The identification of the image of the lift is the identity on ambient schemes. -/
@[simp]
theorem Thickening.levelLiftViaIso_hom_targetHom {e : ℕ} (he : S.IsLevel e) (V : Thickening S)
    (φ : V.thickening.target ⟶ (S.levelSituation he).S) (hφ : φ ≫ S.levelProj he = V.toBase) :
    (V.levelLiftViaIso S he φ hφ).hom.targetHom = 𝟙 _ := rfl

/-- Its inverse is the identity on thickened schemes. -/
@[simp]
theorem Thickening.levelLiftViaIso_inv_sourceHom {e : ℕ} (he : S.IsLevel e) (V : Thickening S)
    (φ : V.thickening.target ⟶ (S.levelSituation he).S) (hφ : φ ≫ S.levelProj he = V.toBase) :
    (V.levelLiftViaIso S he φ hφ).inv.sourceHom = 𝟙 _ := rfl

/-- Its inverse is the identity on ambient schemes. -/
@[simp]
theorem Thickening.levelLiftViaIso_inv_targetHom {e : ℕ} (he : S.IsLevel e) (V : Thickening S)
    (φ : V.thickening.target ⟶ (S.levelSituation he).S) (hφ : φ ≫ S.levelProj he = V.toBase) :
    (V.levelLiftViaIso S he φ hφ).inv.targetHom = 𝟙 _ := rfl

/-- **A morphism of `CRIS(X/S)` between images under `u_e` lifts to `CRIS(X/S_e)`**, with the same
components: the compatibility with the structure morphisms to `S_e` follows from that to `S`
because `S_e ⟶ S` is a monomorphism. -/
def levelChangeBasePreimage {e : ℕ} (he : S.IsLevel e) {A B : Thickening (S.levelSituation he)}
    (k : (S.levelChangeBase he).obj A ⟶ (S.levelChangeBase he).obj B) : A ⟶ B where
  sourceHom := k.sourceHom
  targetHom := k.targetHom
  immersion_naturality := k.immersion_naturality
  base_naturality := (cancel_mono (S.levelProj he)).1
    ((Category.assoc k.targetHom B.toBase (S.levelProj he)).trans k.base_naturality)
  toX_naturality := by simpa using k.toX_naturality

/-- **`u_e : CRIS(X/S_e) ⥤ CRIS(X/S)` is fully faithful**, `S_e ⟶ S` being a monomorphism. -/
def levelChangeBaseFullyFaithful {e : ℕ} (he : S.IsLevel e) :
    (S.levelChangeBase he).FullyFaithful where
  preimage k := S.levelChangeBasePreimage he k
  map_preimage k := by apply Thickening.Hom.ext <;> rfl
  preimage_map k := by apply Thickening.Hom.ext <;> rfl

/-- `u_e` is full. -/
instance full_levelChangeBase {e : ℕ} (he : S.IsLevel e) : (S.levelChangeBase he).Full :=
  (S.levelChangeBaseFullyFaithful he).full

/-- `u_e` is faithful. -/
instance faithful_levelChangeBase {e : ℕ} (he : S.IsLevel e) :
    (S.levelChangeBase he).Faithful :=
  (S.levelChangeBaseFullyFaithful he).faithful

/-- **`u_e` is sieve-like**: an object of `CRIS(X/S)` with a morphism to the image of an object of
`CRIS(X/S_e)` is itself in the image, its structure morphism factoring through `S_e`. -/
abbrev Thickening.levelLiftOfHom {e : ℕ} (he : S.IsLevel e) {Z : Thickening S}
    {W : Thickening (S.levelSituation he)} (k : Z ⟶ (S.levelChangeBase he).obj W) :
    Thickening (S.levelSituation he) :=
  Z.levelLiftVia S he (k.targetHom ≫ W.toBase)
    ((Category.assoc k.targetHom W.toBase (S.levelProj he)).trans k.base_naturality)

/-- The lift of a morphism into the image of `u_e`. -/
def Thickening.levelLiftOfHomHom {e : ℕ} (he : S.IsLevel e) {Z : Thickening S}
    {W : Thickening (S.levelSituation he)} (k : Z ⟶ (S.levelChangeBase he).obj W) :
    Z.levelLiftOfHom S he k ⟶ W :=
  S.levelChangeBasePreimage he ((Z.levelLiftViaIso S he (k.targetHom ≫ W.toBase)
    ((Category.assoc k.targetHom W.toBase (S.levelProj he)).trans k.base_naturality)).hom ≫ k)

/-- **The slice functors of `u_e` are equivalences**: `CRIS(X/S_e)/W ⥤ CRIS(X/S)/u_e(W)` is fully
faithful because `u_e` is, and essentially surjective because `u_e` is sieve-like. -/
instance isEquivalence_overPost_levelChangeBase {e : ℕ} (he : S.IsLevel e)
    (W : Thickening (S.levelSituation he)) :
    (Over.post (X := W) (S.levelChangeBase he)).IsEquivalence where
  essSurj := ⟨fun y => ⟨Over.mk (y.left.levelLiftOfHomHom S he y.hom),
    ⟨Over.isoMk (y.left.levelLiftViaIso S he (y.hom.targetHom ≫ W.toBase)
      ((Category.assoc y.hom.targetHom W.toBase (S.levelProj he)).trans
        y.hom.base_naturality)) (by apply Thickening.Hom.ext <;> exact Category.id_comp _)⟩⟩⟩

end Level

end Crystalline.GlobalCrystallineSituation
