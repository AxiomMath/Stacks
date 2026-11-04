module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackTowerData
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackRelocalizeEquivalence

/-!
# Grothendieck existence on a tower of thickenings in `Coh_{X/Y}`

Let `f : X ⟶ Y` be a separated finitely presented morphism of algebraic spaces over `S`, and
let `ξₙ` be a system of objects of `Coh_{X/Y}` over the spectra `Spec Aₙ` of an inverse system of
algebras with surjective square-zero transitions, mapping compatibly to a test scheme `T` over
`Y` identified with `Spec (lim Aₙ)`. Read `X_T` over `Spec (lim Aₙ)` (Stacks 04SG); its
infinitesimal base changes are the `X_{T_n}`
(`AlgebraicGeometry.Space.CoherentSituation.TowerData.levelIso`), so the modules of the `ξₙ`
make up the standing data of Grothendieck's existence theorem (Stacks 0CX4). Its conclusion
(Stacks 0CXB) gives an object of `Coh_{X/Y}` over `T` restricting to the `ξₙ` compatibly with
the transitions: this is `AlgebraicGeometry.Space.CoherentSituation.TowerExistence`, the input
of the square-zero effectivity of `Coh_{X/Y}` in the proof of Stacks 09DS.

The comparisons are organized by the notion of a family of restrictions of one object compatible
with a tower of identifications (`CategoryTheory.IsTowerRestriction`), which is carried along
functors commuting with the restrictions (`CategoryTheory.IsTowerRestriction.transfer`).

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.towerExistence_of_existence`: Stacks 0CXB gives
  `AlgebraicGeometry.Space.CoherentSituation.TowerExistence` for a separated standing datum.

## References

* [Stacks Project, Tag 0CXB](https://stacks.math.columbia.edu/tag/0CXB)
* [Stacks Project, Tag 0CX4](https://stacks.math.columbia.edu/tag/0CX4)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

attribute [local instance] AlgebraicGeometry.Space.CoherentSituation.towerCategory

/-! ### Compatible families of restrictions -/

namespace CategoryTheory

variable {𝒜 : Type*} [Category* 𝒜] {𝒵 : ℕ → Type*} [∀ n, Category* (𝒵 n)]

/-- A fully faithful functor maps the preimage of an isomorphism `t` to `t`. -/
theorem Functor.FullyFaithful.map_hom_of_eq_preimageIso {𝒞 𝒟 : Type*} [Category* 𝒞]
    [Category* 𝒟] {F : 𝒞 ⥤ 𝒟} (hF : F.FullyFaithful) {X Y : 𝒞} (t : F.obj X ≅ F.obj Y)
    (φ : X ≅ Y) (hφ : φ = hF.preimageIso t) : F.map φ.hom = t.hom := by
  subst hφ
  exact hF.map_preimage t.hom

/-- **A family of restrictions of `G` compatible with a tower.** Restrictions `Pₙ : 𝒜 ⥤ 𝒵ₙ`
with transitions `Qₙ : 𝒵ₙ₊₁ ⥤ 𝒵ₙ` and comparisons `cₙ : Pₙ ≅ Pₙ₊₁ ⋙ Qₙ`; a system of objects
`Fₙ` with `φₙ : Qₙ Fₙ₊₁ ≅ Fₙ`; and identifications `αₙ : Pₙ G ≅ Fₙ` which commute with the
`cₙ` and the `φₙ`. -/
def IsTowerRestriction (P : ∀ n, 𝒜 ⥤ 𝒵 n) (Q : ∀ n, 𝒵 (n + 1) ⥤ 𝒵 n)
    (c : ∀ n, P n ≅ P (n + 1) ⋙ Q n) (F : ∀ n, 𝒵 n) (φ : ∀ n, (Q n).obj (F (n + 1)) ≅ F n)
    (G : 𝒜) (α : ∀ n, (P n).obj G ≅ F n) : Prop :=
  ∀ n, (c n).hom.app G ≫ (Q n).map (α (n + 1)).hom ≫ (φ n).hom = (α n).hom

namespace IsTowerRestriction

variable {P : ∀ n, 𝒜 ⥤ 𝒵 n} {Q : ∀ n, 𝒵 (n + 1) ⥤ 𝒵 n} {c : ∀ n, P n ≅ P (n + 1) ⋙ Q n}
  {F : ∀ n, 𝒵 n} {φ : ∀ n, (Q n).obj (F (n + 1)) ≅ F n} {G : 𝒜} {α : ∀ n, (P n).obj G ≅ F n}

/-- **Compatible restrictions are carried along functors commuting with the restrictions.** -/
theorem transfer (hα : IsTowerRestriction P Q c F φ G α)
    {𝒜' : Type*} [Category* 𝒜'] {𝒵' : ℕ → Type*} [∀ n, Category* (𝒵' n)]
    {P' : ∀ n, 𝒜' ⥤ 𝒵' n} {Q' : ∀ n, 𝒵' (n + 1) ⥤ 𝒵' n} (c' : ∀ n, P' n ≅ P' (n + 1) ⋙ Q' n)
    (U : 𝒜 ⥤ 𝒜') (V : ∀ n, 𝒵 n ⥤ 𝒵' n) (σ : ∀ n, U ⋙ P' n ≅ P n ⋙ V n)
    (ρ : ∀ n, V (n + 1) ⋙ Q' n ≅ Q n ⋙ V n)
    (hc : ∀ n, σ n ≪≫ Functor.isoWhiskerRight (c n) (V n) =
      Functor.isoWhiskerLeft U (c' n) ≪≫ Functor.isoWhiskerRight (σ (n + 1)) (Q' n) ≪≫
        Functor.isoWhiskerLeft (P (n + 1)) (ρ n)) :
    IsTowerRestriction P' Q' c' (fun n => (V n).obj (F n))
      (fun n => (ρ n).app (F (n + 1)) ≪≫ (V n).mapIso (φ n)) (U.obj G)
      (fun n => (σ n).app G ≪≫ (V n).mapIso (α n)) := by
  intro n
  have e := NatTrans.congr_app (congrArg Iso.hom (hc n)) G
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.comp_obj] at e
  have nρ := (ρ n).hom.naturality (α (n + 1)).hom
  simp only [Functor.comp_obj, Functor.comp_map] at nρ
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% nρ, ← reassoc_of% e, ← hα n]
  simp only [Functor.map_comp]

/-- **Compatible restrictions are carried along identifications of the systems.** -/
theorem ofIso (hα : IsTowerRestriction P Q c F φ G α) {F' : ∀ n, 𝒵 n}
    {φ' : ∀ n, (Q n).obj (F' (n + 1)) ≅ F' n} (θ : ∀ n, F n ≅ F' n)
    (hθ : ∀ n, (Q n).map (θ (n + 1)).hom ≫ (φ' n).hom = (φ n).hom ≫ (θ n).hom) :
    IsTowerRestriction P Q c F' φ' G (fun n => α n ≪≫ θ n) := by
  intro n
  simp only [Iso.trans_hom, Functor.map_comp, Category.assoc, hθ n]
  rw [← hα n]
  simp only [Category.assoc]

/-- **Compatible restrictions carried along fully faithful functors**, the transitions of the
source system being the preimages of those of the target system. -/
theorem transfer_preimage (hα : IsTowerRestriction P Q c F φ G α)
    {𝒜' : Type*} [Category* 𝒜'] {𝒵' : ℕ → Type*} [∀ n, Category* (𝒵' n)]
    {P' : ∀ n, 𝒜' ⥤ 𝒵' n} {Q' : ∀ n, 𝒵' (n + 1) ⥤ 𝒵' n} (c' : ∀ n, P' n ≅ P' (n + 1) ⋙ Q' n)
    (U : 𝒜 ⥤ 𝒜') (V : ∀ n, 𝒵 n ⥤ 𝒵' n) (σ : ∀ n, U ⋙ P' n ≅ P n ⋙ V n)
    (ρ : ∀ n, V (n + 1) ⋙ Q' n ≅ Q n ⋙ V n)
    (hc : ∀ n, σ n ≪≫ Functor.isoWhiskerRight (c n) (V n) =
      Functor.isoWhiskerLeft U (c' n) ≪≫ Functor.isoWhiskerRight (σ (n + 1)) (Q' n) ≪≫
        Functor.isoWhiskerLeft (P (n + 1)) (ρ n))
    (hV : ∀ n, (V n).FullyFaithful) (F' : ∀ n, 𝒵' n)
    (φ' : ∀ n, (Q' n).obj (F' (n + 1)) ≅ F' n) (θ : ∀ n, (V n).obj (F n) ≅ F' n)
    (hφ : ∀ n, φ n = (hV n).preimageIso (((ρ n).app (F (n + 1))).symm ≪≫
      (Q' n).mapIso (θ (n + 1)) ≪≫ φ' n ≪≫ (θ n).symm)) :
    IsTowerRestriction P' Q' c' F' φ' (U.obj G)
      (fun n => ((σ n).app G ≪≫ (V n).mapIso (α n)) ≪≫ θ n) :=
  (hα.transfer c' U V σ ρ hc).ofIso θ (fun n => by
    rw [hφ n, Iso.trans_hom, Functor.mapIso_hom,
      Functor.FullyFaithful.map_hom_of_eq_preimageIso (hV n) _ _ rfl]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc])

/-- **Compatible restrictions carried along pasted squares**: the transport is a composite
`E ⋙ I`, its squares are pastings of squares for `E` and for `I` satisfying the composition laws
of `CategoryTheory.Functor.pasteSquare_comp`, and the transitions of the source system are the
preimages of those of the target system. -/
theorem exists_of_paste (hα : IsTowerRestriction P Q c F φ G α)
    {𝒜' : Type*} [Category* 𝒜'] {𝒵' : ℕ → Type*} [∀ n, Category* (𝒵' n)]
    {P' : ∀ n, 𝒜' ⥤ 𝒵' n} {Q' : ∀ n, 𝒵' (n + 1) ⥤ 𝒵' n} (c' : ∀ n, P' n ≅ P' (n + 1) ⋙ Q' n)
    {ℬ : Type*} [Category* ℬ] {ℬn : ℕ → Type*} [∀ n, Category* (ℬn n)]
    (E : 𝒜 ⥤ ℬ) (En : ∀ n, 𝒵 n ⥤ ℬn n) (I : ℬ ⥤ 𝒜') (In : ∀ n, ℬn n ⥤ 𝒵' n)
    {R : ∀ n, ℬ ⥤ ℬn n} {Rt : ∀ n, ℬn (n + 1) ⥤ ℬn n} (μ : ∀ n, R n ≅ R (n + 1) ⋙ Rt n)
    (ρ : ∀ n, E ⋙ R n ≅ P n ⋙ En n) (ρt : ∀ n, En (n + 1) ⋙ Rt n ≅ Q n ⋙ En n)
    (sq : ∀ n, I ⋙ P' n ≅ R n ⋙ In n) (sqt : ∀ n, In (n + 1) ⋙ Q' n ≅ Rt n ⋙ In n)
    (hρ : ∀ n, ρ n ≪≫ Functor.isoWhiskerRight (c n) (En n) =
      Functor.isoWhiskerLeft E (μ n) ≪≫ Functor.isoWhiskerRight (ρ (n + 1)) (Rt n) ≪≫
        Functor.isoWhiskerLeft (P (n + 1)) (ρt n))
    (hs : ∀ n, sq n ≪≫ Functor.isoWhiskerRight (μ n) (In n) =
      Functor.isoWhiskerLeft I (c' n) ≪≫ Functor.isoWhiskerRight (sq (n + 1)) (Q' n) ≪≫
        Functor.isoWhiskerLeft (R (n + 1)) (sqt n))
    (hV : ∀ n, (En n ⋙ In n).FullyFaithful) (F' : ∀ n, 𝒵' n)
    (φ' : ∀ n, (Q' n).obj (F' (n + 1)) ≅ F' n) (θ : ∀ n, (En n ⋙ In n).obj (F n) ≅ F' n)
    (hφ : ∀ n, φ n = (hV n).preimageIso
      (((Functor.pasteSquare (ρt n) (sqt n)).app (F (n + 1))).symm ≪≫
        (Q' n).mapIso (θ (n + 1)) ≪≫ φ' n ≪≫ (θ n).symm)) :
    ∃ ψ : ∀ n, (P' n).obj ((E ⋙ I).obj G) ≅ F' n,
      IsTowerRestriction P' Q' c' F' φ' ((E ⋙ I).obj G) ψ :=
  ⟨_, hα.transfer_preimage c' (E ⋙ I) (fun n => En n ⋙ In n)
    (fun n => Functor.pasteSquare (ρ n) (sq n)) (fun n => Functor.pasteSquare (ρt n) (sqt n))
    (fun n => Functor.pasteSquare_comp (c n) (μ n) (c' n) (ρt n) (ρ (n + 1)) (ρ n) (sqt n)
      (sq (n + 1)) (sq n) (hρ n) (hs n)) hV F' φ' θ hφ⟩

end IsTowerRestriction

end CategoryTheory

/-! ### The conclusion of Stacks 0CXB -/

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] pointTopology

/-- The conclusion of Stacks 0CXB, read as a family of restrictions compatible with the tower of
infinitesimal base changes. -/
theorem InverseSystemExistenceSituation.isTowerRestriction_of_eq
    (s : InverseSystemExistenceSituation.{u})
    (F : Modules.{u, u} s.B (limitBase s.system) s.containsLimitBase s.X.left.1 s.X.left.2)
    (α : ∀ n : ℕ, (modulePullback s.B (limitBase s.system) s.containsLimitBase
      (spaceProjection s.system s.B s.containsLimitBase s.containsBaseAt s.X n)).obj F ≅
        (s.sheaf n).obj)
    (hα : ∀ n : ℕ,
      (modulePullback s.B (limitBase s.system) s.containsLimitBase
          (transitionSpace s.system s.B s.containsLimitBase s.containsBaseAt s.X n)).map
            (α (n + 1)).hom ≫ (s.φ n).hom =
        (modulePullbackCompIso s.B (limitBase s.system) s.containsLimitBase
            (transitionSpace s.system s.B s.containsLimitBase s.containsBaseAt s.X n)
            (spaceProjection s.system s.B s.containsLimitBase s.containsBaseAt s.X
              (n + 1))).hom.app F ≫
          eqToHom (congrArg (fun g => (modulePullback s.B (limitBase s.system)
            s.containsLimitBase g).obj F)
            (transitionSpace_spaceProjection s.system s.B s.containsLimitBase
              s.containsBaseAt s.X n)) ≫
          (α n).hom) :
    IsTowerRestriction
      (fun n => modulePullback s.B (limitBase s.system) s.containsLimitBase
        (spaceProjection s.system s.B s.containsLimitBase s.containsBaseAt s.X n))
      (fun n => modulePullback s.B (limitBase s.system) s.containsLimitBase
        (transitionSpace s.system s.B s.containsLimitBase s.containsBaseAt s.X n))
      (fun n => modulePullbackTriangle s.B (limitBase s.system) s.containsLimitBase
        (transitionSpace_spaceProjection s.system s.B s.containsLimitBase s.containsBaseAt s.X n))
      (fun n => (s.sheaf n).obj) s.φ F α := by
  intro n
  beta_reduce
  rw [hα n, modulePullbackTriangle_eq, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_app_assoc, eqToIso.hom, eqToHom_app, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]

end AlgebraicGeometry.Space

/-! ### Compatible restrictions as morphisms of `Coh_{X/Y}` -/

namespace AlgebraicGeometry.Space.CoherentSituation

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

/-- The composite of two morphisms of `Coh_{X/Y}`, written as a structure. -/
theorem CoherentHom.comp_eq_mk {A A' A'' : CoherentObject D} (m : CoherentHom A A')
    (n : CoherentHom A' A'') :
    m.comp n = ⟨m.base ≫ n.base,
      (D.compComparison m.base n.base).hom.app A''.F ≫
        (modulePullback B S hS (D.relativeMap m.base)).map n.fibre ≫ m.fibre,
      (m.comp n).isIso_fibre⟩ :=
  rfl

/-- **A compatible pair of restrictions is a commuting triangle in `Coh_{X/Y}`.** If a morphism
`n : A' ⟶ Z` and a module comparison `f` along `b = m.base ≫ n.base` commute with the module
comparison of `m`, then `m` followed by `n` is the morphism given by `b` and `f`. -/
theorem coherentHom_comp_eq_of_compatible {A A' Z : CoherentObject D} (m : CoherentHom A A')
    (n : CoherentHom A' Z) {b : A.T ⟶ Z.T} (hb : m.base ≫ n.base = b)
    (f : (modulePullback B S hS (D.relativeMap b)).obj Z.F ⟶ A.F) [IsIso f]
    (τc : modulePullback B S hS (D.relativeMap b) ≅
      modulePullback B S hS (D.relativeMap n.base) ⋙ modulePullback B S hS (D.relativeMap m.base))
    (hkk : D.relativeMap b = D.relativeMap (m.base ≫ n.base))
    (hτ : τc = eqToIso (congrArg (modulePullback B S hS) hkk) ≪≫ D.compComparison m.base n.base)
    (h : τc.hom.app Z.F ≫ (modulePullback B S hS (D.relativeMap m.base)).map n.fibre ≫
      (@asIso _ _ _ _ m.fibre (CoherentHom.isIso_fibre m)).hom = f) :
    m.comp n = (⟨b, f, inferInstance⟩ : CoherentHom A Z) := by
  subst hb
  rw [eqToIso_refl, Iso.refl_trans] at hτ
  rw [asIso_hom] at h
  subst hτ h
  exact CoherentHom.comp_eq_mk m n

/-- If `g ≫ g' = g''`, the base change maps of `f` along `g` and `g'` compose to the base change
map along `g''`. -/
theorem relativeMap_comp_of_eq {T T' T'' : SchemesOver D.Y} {g : T ⟶ T'} {g' : T' ⟶ T''}
    {g'' : T ⟶ T''} (hg : g ≫ g' = g'') :
    D.relativeMap g ≫ D.relativeMap g' = D.relativeMap g'' :=
  (baseChangeMap_comp D.f g g').symm.trans (congrArg (baseChangeMap D.f) hg)

attribute [local instance] towerCategory in
/-- `AlgebraicGeometry.Space.CoherentSituation.coherentHom_comp_eq_of_compatible`, with the
second morphism given by its base map and its module comparison. -/
theorem coherentHom_comp_mk_eq_of_compatible {A A' Z : CoherentObject D} (m : CoherentHom A A')
    {bn : A'.T ⟶ Z.T} (fn : (modulePullback B S hS (D.relativeMap bn)).obj Z.F ⟶ A'.F) [IsIso fn]
    {b : A.T ⟶ Z.T} (hb : m.base ≫ bn = b)
    (f : (modulePullback B S hS (D.relativeMap b)).obj Z.F ⟶ A.F) [IsIso f]
    (τc : modulePullback B S hS (D.relativeMap b) ≅
      modulePullback B S hS (D.relativeMap bn) ⋙ modulePullback B S hS (D.relativeMap m.base))
    (hkk : D.relativeMap b = D.relativeMap (m.base ≫ bn))
    (hτ : τc = eqToIso (congrArg (modulePullback B S hS) hkk) ≪≫ D.compComparison m.base bn)
    (h : τc.hom.app Z.F ≫ (modulePullback B S hS (D.relativeMap m.base)).map fn ≫
      (@asIso _ _ _ _ m.fibre (CoherentHom.isIso_fibre m)).hom = f) :
    m.comp (⟨bn, fn, inferInstance⟩ : CoherentHom A' Z) =
      (⟨b, f, inferInstance⟩ : CoherentHom A Z) :=
  coherentHom_comp_eq_of_compatible m ⟨bn, fn, inferInstance⟩ hb f τc hkk hτ h

attribute [local instance] towerCategory in
/-- **Restrictions compatible with a system of `Coh_{X/Y}` give a cocone.** -/
theorem coherentHom_comp_eq_of_isTowerRestriction (ξ : ℕ ⥤ CoherentObject D)
    (Z : CoherentObject D) (b : ∀ n, (ξ.obj n).T ⟶ Z.T)
    (hb : ∀ n, (ξ.map (homOfLE (n.le_add_right 1)) : CoherentHom _ _).base ≫ b (n + 1) = b n)
    (ψ : ∀ n, (modulePullback B S hS (D.relativeMap (b n))).obj Z.F ≅ (ξ.obj n).F)
    (hψ : IsTowerRestriction (fun n => modulePullback B S hS (D.relativeMap (b n)))
      (fun n => modulePullback B S hS
        (D.relativeMap (ξ.map (homOfLE (n.le_add_right 1)) : CoherentHom _ _).base))
      (fun n => modulePullbackTriangle B S hS (D.relativeMap_comp_of_eq (hb n)))
      (fun n => (ξ.obj n).F)
      (fun n => @asIso _ _ _ _ (ξ.map (homOfLE (n.le_add_right 1)) : CoherentHom _ _).fibre
        (CoherentHom.isIso_fibre _)) Z.F ψ)
    (n : ℕ) :
    (ξ.map (homOfLE (n.le_add_right 1)) : CoherentHom _ _).comp
        ⟨b (n + 1), (ψ (n + 1)).hom, inferInstance⟩ = ⟨b n, (ψ n).hom, inferInstance⟩ :=
  by
  refine coherentHom_comp_mk_eq_of_compatible _ _ (hb n) _
    (modulePullbackTriangle B S hS (D.relativeMap_comp_of_eq (hb n)))
    (congrArg (baseChangeMap D.f) (hb n).symm)
    (modulePullbackTriangle_congr _ (baseChangeMap_comp D.f _ _).symm
      (congrArg (baseChangeMap D.f) (hb n).symm)) ?_
  exact hψ n

end AlgebraicGeometry.Space.CoherentSituation

/-! ### The transport of the tower of infinitesimal base changes to `S` -/

namespace AlgebraicGeometry.Space.CoherentSituation.TowerData

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  (τ : D.TowerData)

/-- The infinitesimal base change of `X_T` at level `n`, over the inverse-limit base. -/
abbrev levelSpace (n : ℕ) : AlgebraicSpaces B (limitBase τ.ringSystem) τ.contains_limitBase :=
  spaceAt τ.ringSystem B τ.contains_limitBase τ.contains_baseAt τ.siteOver n

/-- Its projection to `X_T`. -/
abbrev levelProjection (n : ℕ) : τ.levelSpace n ⟶ τ.siteSpace :=
  spaceProjection τ.ringSystem B τ.contains_limitBase τ.contains_baseAt τ.siteOver n

/-- The transition between consecutive levels. -/
abbrev levelTransition (n : ℕ) : τ.levelSpace n ⟶ τ.levelSpace (n + 1) :=
  transitionSpace τ.ringSystem B τ.contains_limitBase τ.contains_baseAt τ.siteOver n

/-- The transition maps of the inverse system of rings are surjective. -/
theorem transition_surjective (n : ℕ) :
    Function.Surjective (τ.ringSystem.map (homOfLE (Nat.le_succ n)).op).hom :=
  τ.hsurj _

/-- The projection of the level `n` to `X_T` is relatively representable. -/
theorem levelProjection_rep (n : ℕ) :
    yoneda.relativelyRepresentable (τ.levelProjection n).hom :=
  (isClosedImmersion_spaceProjection τ.ringSystem B τ.contains_limitBase τ.contains_baseAt
    τ.siteOver τ.transition_surjective n).rep

/-- The transition from the level `n` to the level `n + 1` is relatively representable. -/
theorem levelTransition_rep (n : ℕ) :
    yoneda.relativelyRepresentable (τ.levelTransition n).hom :=
  (isClosedImmersion_transitionSpace τ.ringSystem B τ.contains_limitBase τ.contains_baseAt
    τ.siteOver τ.transition_surjective n).rep

/-- The identification `Λ X_T ≅ X_T` of Stacks 04SG. -/
abbrev siteIso := siteChangeIso B (D.space τ.T) τ.toBase

/-- The relocalization of modules on a space over the inverse-limit base. -/
abbrev relocModules (Y : AlgebraicSpaces B (limitBase τ.ringSystem) τ.contains_limitBase) :=
  relocalizeModulesEquivalenceSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor Y.2
    (relocalizeSpaceSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor Y).2

/-- **The transport of modules from `X_T` over `Spec A` to `X_T` over `S`.** -/
abbrev limitTransport :
    Modules.{u, u} B (limitBase τ.ringSystem) τ.contains_limitBase τ.siteSpace.1 τ.siteSpace.2 ⥤
      Modules.{u, u} B S hS (D.space τ.T).1 (D.space τ.T).2 :=
  (τ.relocModules τ.siteSpace).functor ⋙ modulePullback B S hS τ.siteIso.inv

/-- The transport of modules on the level `n` to `X_{T_n}`. -/
abbrev levelTransport (n : ℕ) :
    Modules.{u, u} B (limitBase τ.ringSystem) τ.contains_limitBase (τ.levelSpace n).1
        (τ.levelSpace n).2 ⥤
      Modules.{u, u} B S hS (D.space (τ.ξ.obj n).T).1 (D.space (τ.ξ.obj n).T).2 :=
  (τ.relocModules (τ.levelSpace n)).functor ⋙ modulePullback B S hS (τ.levelIso n).inv

/-- The inverse image along `X_{T_n} ≅ Λ Xₙ`, an equivalence. -/
def levelPullbackEquivalence (n : ℕ) :=
  (modulePushforwardCoherence B S hS).modulePullbackEquivalence
    (⟨(τ.levelIso n).inv, (τ.levelIso n).hom, (τ.levelIso n).inv_hom_id,
      (τ.levelIso n).hom_inv_id⟩ : D.space (τ.ξ.obj n).T ≅ _)

/-- **The transport of modules on the level `n` to `X_{T_n}` is fully faithful.** -/
def levelTransportFullyFaithful (n : ℕ) : (τ.levelTransport n).FullyFaithful :=
  (τ.relocModules (τ.levelSpace n)).fullyFaithfulFunctor.comp
    (τ.levelPullbackEquivalence n).fullyFaithfulFunctor

/-- The base map of the transition of `ξ`. -/
abbrev baseTransition (n : ℕ) : (τ.ξ.obj n).T ⟶ (τ.ξ.obj (n + 1)).T :=
  (τ.ξ.map (homOfLE (n.le_add_right 1)) : CoherentHom (τ.ξ.obj n) (τ.ξ.obj (n + 1))).base

/-- The base change map along the transition of `ξ` followed by the one along `b (n + 1)` is the
base change map along `b n`. -/
theorem relativeMap_comp (n : ℕ) :
    D.relativeMap (τ.baseTransition n) ≫ D.relativeMap (τ.b (n + 1)) = D.relativeMap (τ.b n) :=
  D.relativeMap_comp_of_eq (τ.hb n)

/-- The identification `X_{T_n} ≅ Λ Xₙ` followed by the relocalized projection to `Λ X_T` is the
base change map along `b n` followed by the identification `X_T ≅ Λ X_T`. -/
theorem levelIso_inv_comp (n : ℕ) :
    (τ.levelIso n).inv ≫ relocalizeHomSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS
        τ.baseMor (τ.levelProjection n) = D.relativeMap (τ.b n) ≫ τ.siteIso.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, τ.levelIso_hom_relativeMap n, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The identification `X_{T_n} ≅ Λ Xₙ` followed by the relocalized transition is the base change
map along the transition of `ξ` followed by the identification `X_{T_{n+1}} ≅ Λ Xₙ₊₁`. -/
theorem levelIso_inv_transition (n : ℕ) :
    (τ.levelIso n).inv ≫ relocalizeHomSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS
        τ.baseMor (τ.levelTransition n) =
      D.relativeMap (τ.baseTransition n) ≫ (τ.levelIso (n + 1)).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← τ.relocalize_transitionSpace_levelIso n,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The relocalized transition from the level `n` followed by the relocalized projection of the
level `n + 1` is the relocalized projection of the level `n`. -/
theorem relocalize_levelTransition_comp (n : ℕ) :
    relocalizeHomSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor
          (τ.levelTransition n) ≫
        relocalizeHomSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor
          (τ.levelProjection (n + 1)) =
      relocalizeHomSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor
        (τ.levelProjection n) :=
  (relocalizeHom_comp τ.baseMor _ _).symm.trans (congrArg _
    (transitionSpace_spaceProjection τ.ringSystem B τ.contains_limitBase τ.contains_baseAt
      τ.siteOver n))

/-- **The transport of modules commutes with the transitions between the levels.** -/
def transitionSquare (n : ℕ) :
    τ.levelTransport (n + 1) ⋙ modulePullback B S hS (D.relativeMap (τ.baseTransition n)) ≅
      modulePullback B (limitBase τ.ringSystem) τ.contains_limitBase (τ.levelTransition n) ⋙
        τ.levelTransport n :=
  Functor.pasteSquare
    (relocalizeModulePullbackIsoSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor
      (τ.levelTransition n) (τ.levelTransition_rep n)).symm
    (modulePullbackSquare B S hS rfl (τ.levelIso_inv_transition n))

/-! ### The standing data of Stacks 0CX4 -/

/-- **The module at level `n`**: the module of `ξ n`, carried to the infinitesimal base change of
`X_T` over the inverse-limit base. -/
abbrev levelModule (n : ℕ) :
    Modules.{u, u} B (limitBase τ.ringSystem) τ.contains_limitBase (τ.levelSpace n).1
      (τ.levelSpace n).2 :=
  (τ.relocModules (τ.levelSpace n)).inverse.obj
    ((modulePullback B S hS (τ.levelIso n).hom).obj (τ.ξ.obj n).F)

/-- The transport of the module at level `n` is the module of `ξ n`. -/
def levelModuleIso (n : ℕ) : (τ.levelTransport n).obj (τ.levelModule n) ≅ (τ.ξ.obj n).F :=
  (modulePullback B S hS (τ.levelIso n).inv).mapIso
      ((τ.relocModules (τ.levelSpace n)).counitIso.app _) ≪≫
    (τ.levelPullbackEquivalence n).counitIso.app _

/-- The module comparison of the transition of `ξ`. -/
def fibreIso (n : ℕ) :
    (modulePullback B S hS (D.relativeMap (τ.baseTransition n))).obj (τ.ξ.obj (n + 1)).F ≅
      (τ.ξ.obj n).F :=
  @asIso _ _ _ _ (τ.ξ.map (homOfLE (n.le_add_right 1)) : CoherentHom _ _).fibre
    (CoherentHom.isIso_fibre _)

/-- The transitions of `ξ`, read on the transports of the modules at the levels. -/
def levelTransitionTarget (n : ℕ) :
    (τ.levelTransport n).obj
        ((modulePullback B (limitBase τ.ringSystem) τ.contains_limitBase (τ.levelTransition n)).obj
          (τ.levelModule (n + 1))) ≅
      (τ.levelTransport n).obj (τ.levelModule n) :=
  ((τ.transitionSquare n).app (τ.levelModule (n + 1))).symm ≪≫
    (modulePullback B S hS (D.relativeMap (τ.baseTransition n))).mapIso
      (τ.levelModuleIso (n + 1)) ≪≫ τ.fibreIso n ≪≫ (τ.levelModuleIso n).symm

/-- **The transitions of the modules at the levels**, carried from the transitions of `ξ`. -/
irreducible_def levelTransitionIso (n : ℕ) :
    (modulePullback B (limitBase τ.ringSystem) τ.contains_limitBase (τ.levelTransition n)).obj
        (τ.levelModule (n + 1)) ≅ τ.levelModule n :=
  (τ.levelTransportFullyFaithful n).preimageIso (τ.levelTransitionTarget n)

/-- The module at level `n` is of finite presentation. -/
theorem isFinitePresentationOnSite_levelModule (n : ℕ) :
    (τ.levelModule n).IsFinitePresentationOnSite :=
  isFinitePresentationOnSite_relocalizeModulesEquivalence_inverse τ.baseMor _
    ((modulePullbackStabilityOfFinitePresentation B S hS).finitePresentation _ _
      (τ.ξ.obj n).finitePresentation)

/-- The identification `Λ Xₙ ≅ X_{T_n}` lies over the identification of the affine base at level
`n` with the test scheme of `ξ n`. -/
theorem isPullback_levelIso (n : ℕ) :
    IsPullback (τ.levelIso n).hom
      (relocalizeHomSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor
        (spaceBaseProjection τ.ringSystem B τ.contains_limitBase τ.contains_baseAt τ.siteOver n))
      (D.projection (τ.ξ.obj n).T)
      (ObjectProperty.isoMk _ (τ.basePresheafIso n) :
          relocalizeSpaceSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor
              (schemeSpace (baseObjectAt τ.ringSystem B τ.contains_limitBase
                τ.contains_baseAt n)) ≅
            (schemeSpaceFunctor B S hS).obj (τ.ξ.obj n).T.left).hom :=
  IsPullback.of_horiz_isIso (CommSq.mk (τ.levelIso_hom_projection n))

/-- The module at level `n` is flat over the affine base at level `n`. -/
theorem isFlatOver_levelModule (n : ℕ) :
    IsFlatOver B (limitBase τ.ringSystem) τ.contains_limitBase (τ.levelSpace n).2
      (spaceBaseProjection τ.ringSystem B τ.contains_limitBase τ.contains_baseAt τ.siteOver n).hom
      (τ.levelModule n) :=
  isFlatOver_relocalizeModulesEquivalence_inverseSE B (limitBase τ.ringSystem) S
    τ.contains_limitBase hS τ.baseMor _ _ _ _
    ((modulePullbackStabilityOfFinitePresentation B S hS).flat (τ.isPullback_levelIso n) _
      (τ.ξ.obj n).finitePresentation (τ.ξ.obj n).flat)

/-- The projection of the level `n` to the affine base at level `n` is locally of finite type. -/
theorem isLocallyOfFiniteType_levelBaseProjection (n : ℕ) :
    IsLocallyOfFiniteType B (limitBase τ.ringSystem) τ.contains_limitBase
      (spaceBaseProjection τ.ringSystem B τ.contains_limitBase τ.contains_baseAt τ.siteOver
        n).hom :=
  isLocallyOfFiniteType_spaceBaseProjection τ.ringSystem B τ.contains_limitBase τ.contains_baseAt
    τ.siteOver (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B (limitBase τ.ringSystem)
      τ.contains_limitBase τ.isFinitePresentation_siteStructure.1) n

/-- The module at level `n` has closed support, proper over the affine base at level `n`. -/
theorem hasProperSupport_levelModule (n : ℕ) :
    HasProperSupport B (limitBase τ.ringSystem) τ.contains_limitBase (τ.levelSpace n).2
      (schemeSpace (baseObjectAt τ.ringSystem B τ.contains_limitBase τ.contains_baseAt n)).2
      (spaceBaseProjection τ.ringSystem B τ.contains_limitBase τ.contains_baseAt τ.siteOver n).hom
      (τ.isLocallyOfFiniteType_levelBaseProjection n)
      ((SheafOfModules.toSheaf _).obj (τ.levelModule n)) := by
  obtain ⟨hp, hU, hproper⟩ := (τ.ξ.obj n).properSupport
  have := (τ.ξ.obj n).finitePresentation
  have := (τ.ξ.obj n).quasicoherent
  obtain ⟨hU', hproper'⟩ := (modulePullbackStabilityOfFinitePresentation B S hS).properSupport
    (τ.isPullback_levelIso n) hp _ inferInstance inferInstance hU hproper
  exact (hasProperSupport_relocalizeModulesEquivalence_inverse_iffSE B (limitBase τ.ringSystem) S
    τ.contains_limitBase hS τ.baseMor _ _ _ _ _ _ _).2 ⟨hU', hproper'⟩

/-- The kernels of the transition maps of the inverse system of rings are locally nilpotent. -/
theorem transition_locallyNilpotent (n : ℕ) :
    (RingHom.ker (τ.ringSystem.map (homOfLE (Nat.le_succ n)).op).hom).LocallyNilpotent := by
  intro x hx
  refine ⟨2, ?_⟩
  have hx' : x * x ∈ RingHom.ker (τ.R.map (homOfLE (Nat.le_succ n)).op).hom.toRingHom ^ 2 := by
    rw [sq]
    exact Ideal.mul_mem_mul hx hx
  rw [τ.hsq] at hx'
  simpa [pow_two] using hx'

/-- **The standing data of Stacks 0CX4 attached to the tower**: the inverse system of rings, `X_T`
over its limit, and the modules of the `ξₙ` on the infinitesimal base changes. -/
def existenceSituation (hsep : IsSeparated B S hS D.f.hom) :
    InverseSystemExistenceSituation.{u} where
  system := τ.ringSystem
  transition_surjective := τ.transition_surjective
  transition_locallyNilpotent := τ.transition_locallyNilpotent
  B := B
  containsLimitBase := τ.contains_limitBase
  containsBaseAt := τ.contains_baseAt
  X := τ.siteOver
  separated := τ.isSeparatedOver_siteSpace hsep
  finitePresentation := τ.isFinitePresentation_siteStructure
  closedSpaceProjection n := isClosedImmersion_spaceProjection τ.ringSystem B τ.contains_limitBase
    τ.contains_baseAt τ.siteOver τ.transition_surjective n
  sheaf n := ⟨τ.levelModule n,
    haveI := τ.isFinitePresentationOnSite_levelModule n
    inferInstance⟩
  finitePresentation_sheaf n := τ.isFinitePresentationOnSite_levelModule n
  flat_sheaf n := τ.isFlatOver_levelModule n
  closed_support n := (τ.hasProperSupport_levelModule n).1
  locallyOfFiniteType n := τ.isLocallyOfFiniteType_levelBaseProjection n
  properSupport n := (τ.hasProperSupport_levelModule n).2
  φ n := τ.levelTransitionIso n

/-! ### The module over the inverse-limit base, read on `X_T` -/

/-- The identification of the test scheme over the limit with `Λ (Spec A)`. -/
def limitTargetIso :
    (schemeSpaceFunctor B S hS).obj τ.T.left ≅
      relocalizeSpaceSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor
        (schemeSpace (limitBaseObject τ.ringSystem B τ.contains_limitBase)) :=
  (schemeSpaceFunctor B S hS).mapIso τ.testIso.symm ≪≫
    (ObjectProperty.isoMk _ (@asIso _ _ _ _ τ.limitTargetMap τ.isIso_limitTargetMap) :
      relocalizeSpaceSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor
          (schemeSpace (limitBaseObject τ.ringSystem B τ.contains_limitBase)) ≅
        (schemeSpaceFunctor B S hS).obj (Over.mk τ.baseMor)).symm

/-- The identification `X_T ≅ Λ X_T` lies over the identification of the test scheme with
`Λ (Spec A)`. -/
theorem siteIso_inv_comp_relocalize :
    τ.siteIso.inv ≫ relocalizeHomSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS
        τ.baseMor τ.siteStructure = D.projection τ.T ≫ τ.limitTargetIso.hom := by
  apply ObjectProperty.hom_ext
  have := τ.isIso_limitTargetMap
  rw [← cancel_mono τ.limitTargetMap]
  have e1 : τ.siteIso.inv.hom ≫ τ.siteIso.hom.hom = 𝟙 _ :=
    congrArg (fun k => k.hom) τ.siteIso.inv_hom_id
  have e2 := τ.relocalize_siteStructure_comp
  have l : (τ.siteIso.inv ≫ relocalizeHomSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS
      τ.baseMor τ.siteStructure).hom ≫ τ.limitTargetMap = τ.toBase.hom :=
    (Category.assoc _ _ _).trans ((congrArg (τ.siteIso.inv.hom ≫ ·) e2).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.toBase.hom) e1).trans
        (Category.id_comp _))))
  have h3 : (yoneda.map τ.testIso.inv ≫ inv τ.limitTargetMap) ≫ τ.limitTargetMap =
      yoneda.map τ.testIso.inv := by
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have r : (D.projection τ.T ≫ τ.limitTargetIso.hom).hom ≫ τ.limitTargetMap =
      τ.toBase.hom := by
    show ((D.projection τ.T).hom ≫ (yoneda.map τ.testIso.inv ≫ inv τ.limitTargetMap)) ≫
      τ.limitTargetMap = _
    exact (Category.assoc _ _ _).trans (congrArg ((D.projection τ.T).hom ≫ ·) h3)
  exact l.trans r.symm

/-- The square formed by the identification `X_T ≅ Λ X_T` over the identification of the test
scheme with `Λ (Spec A)` is a pullback. -/
theorem isPullback_siteIso_inv :
    IsPullback τ.siteIso.inv (D.projection τ.T)
      (relocalizeHomSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor
        τ.siteStructure) τ.limitTargetIso.hom :=
  IsPullback.of_horiz_isIso (CommSq.mk τ.siteIso_inv_comp_relocalize)

variable (F : Modules.{u, u} B (limitBase τ.ringSystem) τ.contains_limitBase τ.siteSpace.1
  τ.siteSpace.2)

/-- The transport to `X_T` over `S` of a module of finite presentation is of finite
presentation. -/
theorem isFinitePresentationOnSite_limitTransport (hF : F.IsFinitePresentationOnSite) :
    (τ.limitTransport.obj F).IsFinitePresentationOnSite :=
  (modulePullbackStabilityOfFinitePresentation B S hS).finitePresentation _ _
    (isFinitePresentationOnSite_relocalizeModulesEquivalence_functor τ.baseMor F hF)

/-- The transport to `X_T` over `S` of a module of finite presentation, flat over `Spec A`, is flat
over `T`. -/
theorem isFlatOver_limitTransport (hF : F.IsFinitePresentationOnSite)
    (hfl : IsFlatOver B (limitBase τ.ringSystem) τ.contains_limitBase τ.siteSpace.2
      τ.siteStructure.hom F) :
    IsFlatOver B S hS (D.space τ.T).2 (D.projection τ.T).hom (τ.limitTransport.obj F) :=
  (modulePullbackStabilityOfFinitePresentation B S hS).flat τ.isPullback_siteIso_inv _
    (isFinitePresentationOnSite_relocalizeModulesEquivalence_functor τ.baseMor F hF)
    (isFlatOver_relocalizeModulesEquivalence_functorSE B (limitBase τ.ringSystem) S
      τ.contains_limitBase hS τ.baseMor τ.siteStructure.hom τ.siteSpace.2 _ F hfl)

/-- The transport to `X_T` over `S` of a module of finite presentation with closed support proper
over `Spec A` has closed support proper over `T`. -/
theorem properSupport_limitTransport (hF : F.IsFinitePresentationOnSite)
    (hcl : IsClosed (supportOfSheaf B (limitBase τ.ringSystem) τ.contains_limitBase
      τ.siteSpace.1 ((SheafOfModules.toSheaf _).obj F)))
    (hprop : IsProperOver B (limitBase τ.ringSystem) τ.contains_limitBase τ.siteSpace.2
      (schemeSpace (limitBaseObject τ.ringSystem B τ.contains_limitBase)).2 τ.siteStructure.hom
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B (limitBase τ.ringSystem)
        τ.contains_limitBase τ.isFinitePresentation_siteStructure.1)
      (supportOfSheaf B (limitBase τ.ringSystem) τ.contains_limitBase τ.siteSpace.1
        ((SheafOfModules.toSheaf _).obj F)) hcl) :
    ∃ (hp : IsLocallyOfFiniteType B S hS (D.projection τ.T).hom)
      (hU : IsClosed (D.support τ.T (τ.limitTransport.obj F))),
      IsProperOver B S hS (D.space τ.T).2
        ((schemeSpaceFunctor B S hS).obj τ.T.left).2 (D.projection τ.T).hom hp
        (D.support τ.T (τ.limitTransport.obj F)) hU := by
  have hf := isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B (limitBase τ.ringSystem)
    τ.contains_limitBase τ.isFinitePresentation_siteStructure.1
  obtain ⟨hU, hp⟩ := (hasProperSupport_relocalizeModulesEquivalence_functor_iffSE B
    (limitBase τ.ringSystem) S τ.contains_limitBase hS τ.baseMor _ _ _ _ _ hf F).2 ⟨hcl, hprop⟩
  have hfpΛ := isFinitePresentationOnSite_relocalizeModulesEquivalence_functor τ.baseMor F hF
  have := hfpΛ
  obtain ⟨hU', hp'⟩ := (modulePullbackStabilityOfFinitePresentation B S hS).properSupport
    τ.isPullback_siteIso_inv
    ((isLocallyOfFiniteType_relocalize_iff B (limitBase τ.ringSystem) τ.contains_limitBase S hS
      τ.baseMor _).2 hf) _ inferInstance inferInstance hU hp
  exact ⟨_, hU', hp'⟩

end AlgebraicGeometry.Space.CoherentSituation.TowerData

/-! ### Stacks 0CXB gives Grothendieck existence on towers in `Coh_{X/Y}` -/

namespace AlgebraicGeometry.Space.CoherentSituation

universe u

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)

/-- **The object over the limit of a tower of thickenings in `Coh_{X/Y}`**, given Stacks 0CXB:
the module of Stacks 0CXB on `X_T` over `Spec (lim Aₙ)`, transported to `X_T` over `S`, with
morphisms from the `ξₙ` forming a cocone. -/
theorem TowerData.exists_object {D : CoherentSituation B S hS} (τ : D.TowerData)
    (h0CXB : ∀ s : InverseSystemExistenceSituation.{u},
      ∃ F : Modules.{u, u} s.B (limitBase s.system) s.containsLimitBase s.X.left.1 s.X.left.2,
          F.IsFinitePresentationOnSite ∧
            IsFlatOver s.B (limitBase s.system) s.containsLimitBase s.X.left.2 s.X.hom.hom F ∧
            ∃ hcl : IsClosed (supportOfSheaf s.B (limitBase s.system) s.containsLimitBase s.X.left.1
                ((SheafOfModules.toSheaf _).obj F)),
              IsProperOver s.B (limitBase s.system) s.containsLimitBase s.X.left.2
                (schemeSpace (limitBaseObject s.system s.B s.containsLimitBase)).2 s.X.hom.hom
                (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation s.B (limitBase s.system)
                  s.containsLimitBase s.finitePresentation.1)
                (supportOfSheaf s.B (limitBase s.system) s.containsLimitBase s.X.left.1
                  ((SheafOfModules.toSheaf _).obj F)) hcl ∧
              ∃ α : ∀ n : ℕ, (modulePullback s.B (limitBase s.system) s.containsLimitBase
                  (spaceProjection s.system s.B s.containsLimitBase s.containsBaseAt s.X n)).obj F ≅
                    (s.sheaf n).obj,
                ∀ n : ℕ,
                  (modulePullback s.B (limitBase s.system) s.containsLimitBase
                      (transitionSpace s.system s.B s.containsLimitBase s.containsBaseAt s.X n)).map
                        (α (n + 1)).hom ≫ (s.φ n).hom =
                    (modulePullbackCompIso s.B (limitBase s.system) s.containsLimitBase
                        (transitionSpace s.system s.B s.containsLimitBase s.containsBaseAt s.X n)
                        (spaceProjection s.system s.B s.containsLimitBase s.containsBaseAt s.X
                          (n + 1))).hom.app F ≫
                      eqToHom (congrArg (fun g => (modulePullback s.B (limitBase s.system)
                        s.containsLimitBase g).obj F)
                        (transitionSpace_spaceProjection s.system s.B s.containsLimitBase
                          s.containsBaseAt s.X n)) ≫
                      (α n).hom)
    (hsep : IsSeparated B S hS D.f.hom) :
    ∃ (G : Modules.{u, u} B S hS (D.space τ.T).1 (D.space τ.T).2)
      (hq : G.IsQuasicoherentOnSite) (hfp : G.IsFinitePresentationOnSite)
      (hfl : IsFlatOver B S hS (D.space τ.T).2 (D.projection τ.T).hom G)
      (hps : ∃ (hp : IsLocallyOfFiniteType B S hS (D.projection τ.T).hom)
        (hU : IsClosed (D.support τ.T G)),
        IsProperOver B S hS (D.space τ.T).2
          ((schemeSpaceFunctor B S hS).obj τ.T.left).2 (D.projection τ.T).hom hp
            (D.support τ.T G) hU)
      (ψ : ∀ n, (modulePullback B S hS (D.relativeMap (τ.b n))).obj G ≅ (τ.ξ.obj n).F),
      ∀ n, ((τ.ξ.map (homOfLE (n.le_add_right 1)) : CoherentHom _ _).comp
          (⟨τ.b (n + 1), (ψ (n + 1)).hom, inferInstance⟩ :
            CoherentHom (τ.ξ.obj (n + 1)) (D.objectOf τ.T G hq hfp hfl hps))) =
        ⟨τ.b n, (ψ n).hom, inferInstance⟩ := by
  obtain ⟨F, hfp, hfl, hcl, hprop, α, hα⟩ := h0CXB (τ.existenceSituation hsep)
  have hW := (τ.existenceSituation hsep).isTowerRestriction_of_eq F α hα
  obtain ⟨ψ, hψ⟩ := hW.exists_of_paste
    (fun n => modulePullbackTriangle B S hS (τ.relativeMap_comp n))
    (τ.relocModules τ.siteSpace).functor (fun n => (τ.relocModules (τ.levelSpace n)).functor)
    (modulePullback B S hS τ.siteIso.inv) (fun n => modulePullback B S hS (τ.levelIso n).inv)
    (fun n => modulePullbackTriangle B S hS (τ.relocalize_levelTransition_comp n))
    (fun n => (relocalizeModulePullbackIsoSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS
      τ.baseMor (τ.levelProjection n) (τ.levelProjection_rep n)).symm)
    (fun n => (relocalizeModulePullbackIsoSE B (limitBase τ.ringSystem) S τ.contains_limitBase hS
      τ.baseMor (τ.levelTransition n) (τ.levelTransition_rep n)).symm)
    (fun n => modulePullbackSquare B S hS rfl (τ.levelIso_inv_comp n))
    (fun n => modulePullbackSquare B S hS rfl (τ.levelIso_inv_transition n))
    (fun n => relocalizeModulePullbackIso_symm_triangle τ.baseMor
      (transitionSpace_spaceProjection τ.ringSystem B τ.contains_limitBase τ.contains_baseAt
        τ.siteOver n) _ _ _ (τ.relocalize_levelTransition_comp n))
    (fun n => modulePullbackSquare_comp (modulePushforwardCoherence B S hS)
      (τ.relativeMap_comp n) (τ.relocalize_levelTransition_comp n) rfl
      (τ.levelIso_inv_transition n) rfl (τ.levelIso_inv_comp (n + 1)) rfl (τ.levelIso_inv_comp n))
    τ.levelTransportFullyFaithful (fun n => (τ.ξ.obj n).F) τ.fibreIso τ.levelModuleIso
    (fun n => TowerData.levelTransitionIso_def τ n)
  have hGfp := τ.isFinitePresentationOnSite_limitTransport F hfp
  have hGfl := τ.isFlatOver_limitTransport F hfp hfl
  have hGps := τ.properSupport_limitTransport F hfp hcl hprop
  have := hGfp
  exact ⟨τ.limitTransport.obj F, inferInstance, hGfp, hGfl, hGps, ψ,
    coherentHom_comp_eq_of_isTowerRestriction τ.ξ
      (D.objectOf τ.T (τ.limitTransport.obj F) inferInstance hGfp hGfl hGps) τ.b τ.hb ψ hψ⟩

/-- **Grothendieck existence on towers of thickenings in `Coh_{X/Y}` from Stacks 0CXB**, for a
separated standing datum. The tower is read on `X_T` over `Spec (lim Aₙ)` (Stacks 04SG), Stacks
0CXB gives a module there restricting to the modules of the tower, and its transport to `X_T`
over `S` is the object over `T`. -/
theorem towerExistence_of_existence
    (h0CXB : ∀ s : InverseSystemExistenceSituation.{u},
      ∃ F : Modules.{u, u} s.B (limitBase s.system) s.containsLimitBase s.X.left.1 s.X.left.2,
          F.IsFinitePresentationOnSite ∧
            IsFlatOver s.B (limitBase s.system) s.containsLimitBase s.X.left.2 s.X.hom.hom F ∧
            ∃ hcl : IsClosed (supportOfSheaf s.B (limitBase s.system) s.containsLimitBase s.X.left.1
                ((SheafOfModules.toSheaf _).obj F)),
              IsProperOver s.B (limitBase s.system) s.containsLimitBase s.X.left.2
                (schemeSpace (limitBaseObject s.system s.B s.containsLimitBase)).2 s.X.hom.hom
                (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation s.B (limitBase s.system)
                  s.containsLimitBase s.finitePresentation.1)
                (supportOfSheaf s.B (limitBase s.system) s.containsLimitBase s.X.left.1
                  ((SheafOfModules.toSheaf _).obj F)) hcl ∧
              ∃ α : ∀ n : ℕ, (modulePullback s.B (limitBase s.system) s.containsLimitBase
                  (spaceProjection s.system s.B s.containsLimitBase s.containsBaseAt s.X n)).obj F ≅
                    (s.sheaf n).obj,
                ∀ n : ℕ,
                  (modulePullback s.B (limitBase s.system) s.containsLimitBase
                      (transitionSpace s.system s.B s.containsLimitBase s.containsBaseAt s.X n)).map
                        (α (n + 1)).hom ≫ (s.φ n).hom =
                    (modulePullbackCompIso s.B (limitBase s.system) s.containsLimitBase
                        (transitionSpace s.system s.B s.containsLimitBase s.containsBaseAt s.X n)
                        (spaceProjection s.system s.B s.containsLimitBase s.containsBaseAt s.X
                          (n + 1))).hom.app F ≫
                      eqToHom (congrArg (fun g => (modulePullback s.B (limitBase s.system)
                        s.containsLimitBase g).obj F)
                        (transitionSpace_spaceProjection s.system s.B s.containsLimitBase
                          s.containsBaseAt s.X n)) ≫
                      (α n).hom)
    (hsep : IsSeparated B S hS D.f.hom) : D.TowerExistence := by
  intro Λ _ R cR hcR hsurj hsq T eT ξ b hb e he hbT
  exact TowerData.exists_object ⟨Λ, R, cR, hcR, hsurj, hsq, T, eT, ξ, b, hb, e, he, hbT⟩ h0CXB hsep

end AlgebraicGeometry.Space.CoherentSituation

end
