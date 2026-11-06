module

public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineBaseReduction
public import StacksFrontier.AlgebraicGeometry.GroupScheme.QuasicoherentPullbackFunctor
public import StacksFrontier.AlgebraicGeometry.Groupoids.Coinduction
public import StacksFrontier.AlgebraicGeometry.Groupoids.Equivariant.PushforwardDescent
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuasicoherentFromBase
public import StacksFrontier.AlgebraicGeometry.Simplicial.GroupoidQuasiCoherentComparison

/-!
# Reindexing and restriction along the identity section

Auxiliary calculus for the adjunction between coinduction and the forgetful functor on
quasi-coherent modules on a groupoid scheme: the reindexing `reindexHom₂` of a morphism between
the pullbacks of two different modules, its coherences with the unit and associativity
isomorphisms of the pullback pseudofunctor, and restriction along the identity section, which
gives the maps `Stacks.Groupoids.GroupoidScheme.transpose` and
`Stacks.Groupoids.GroupoidScheme.untranspose` with `untranspose_transpose`.

## References

* [Stacks Project, Tag 07TR](https://stacks.math.columbia.edu/tag/07TR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.AffinePushforward (baseChangeNatTrans)
open Stacks.AlgebraicGeometry.FlatBaseChangeCohomology (pasteBase
  baseChangeNatTrans_pasteBase_app isIso_baseChangeNatTrans_of_flat)

universe u

set_option synthInstance.maxHeartbeats 200000

namespace Stacks.Groupoids.GroupoidScheme

/-! ### The hom-set bijection -/


/-! ### Reindexing a morphism between pullbacks of two different modules -/

/-- Pull a morphism between the pullbacks of two modules along two morphisms back once more,
with the canonical identifications of the iterated pullbacks with the pullbacks along the
corresponding composites.  This is `Stacks.Groupoids.reindexHom` with the two modules allowed
to differ. -/
noncomputable def reindexHom₂ {X Y Z : Scheme.{u}} (f : X ⟶ Y) {g h : Y ⟶ Z}
    {F F' : Z.Modules}
    (ψ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback h).obj F') :
    (Scheme.Modules.pullback (f ≫ g)).obj F ⟶ (Scheme.Modules.pullback (f ≫ h)).obj F' :=
  (Scheme.Modules.pullbackComp f g).inv.app F ≫ (Scheme.Modules.pullback f).map ψ ≫
    (Scheme.Modules.pullbackComp f h).hom.app F'

/-- On a morphism between pullbacks of a single module, reindexing agrees with
`Stacks.Groupoids.reindexHom`. -/
theorem reindexHom₂_eq_reindexHom {X Y Z : Scheme.{u}} (f : X ⟶ Y) {g h : Y ⟶ Z}
    {F : Z.Modules}
    (α : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback h).obj F) :
    reindexHom₂ f α = Stacks.Groupoids.reindexHom f α :=
  rfl

/-- Reindexing is compatible with composition. -/
@[reassoc]
theorem reindexHom₂_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) {g h k : Y ⟶ Z}
    {F F' F'' : Z.Modules}
    (ψ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback h).obj F')
    (χ : (Scheme.Modules.pullback h).obj F' ⟶ (Scheme.Modules.pullback k).obj F'') :
    reindexHom₂ f (ψ ≫ χ) = reindexHom₂ f ψ ≫ reindexHom₂ f χ := by
  simp [reindexHom₂]

/-- Reindexing the inverse image of a morphism of modules is the inverse image along the
composite. -/
theorem reindexHom₂_pullback_map {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {F F' : Z.Modules} (i : F ⟶ F') :
    reindexHom₂ f ((Scheme.Modules.pullback g).map i) =
      (Scheme.Modules.pullback (f ≫ g)).map i := by
  have h := (Scheme.Modules.pullbackComp f g).hom.naturality i
  simp only [Functor.comp_map] at h
  rw [reindexHom₂, h, Iso.inv_hom_id_app_assoc]

/-- Reindexing the canonical comparison of pullbacks along equal morphisms is again such a
comparison, for the composites. -/
theorem reindexHom₂_congr {X Y Z : Scheme.{u}} (f : X ⟶ Y) {g h : Y ⟶ Z} (p : g = h)
    (F : Z.Modules) :
    reindexHom₂ f ((Scheme.Modules.pullbackCongr p).hom.app F) =
      (Scheme.Modules.pullbackCongr (congrArg (fun x ↦ f ≫ x) p)).hom.app F := by
  cases p
  simp [reindexHom₂, Scheme.Modules.pullbackCongr]

/-- Replacing the reindexing morphism by an equal one conjugates the result by the canonical
comparisons of the pullbacks along the two resulting composites. -/
theorem reindexHom₂_congr_source {X Y Z : Scheme.{u}} {f f' : X ⟶ Y} (p : f = f')
    {g h : Y ⟶ Z} {F F' : Z.Modules}
    (ψ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback h).obj F') :
    reindexHom₂ f ψ =
      (Scheme.Modules.pullbackCongr (congrArg (fun x ↦ x ≫ g) p)).hom.app F ≫
        reindexHom₂ f' ψ ≫
        (Scheme.Modules.pullbackCongr (congrArg (fun x ↦ x ≫ h) p).symm).hom.app F' := by
  cases p
  simp [Scheme.Modules.pullbackCongr]

/-! ### The two unit coherences of the pullback pseudofunctor, componentwise -/

/-- The right unitality coherence of the pullback pseudofunctor, at a module. -/
private theorem pullbackComp_id_left_inv_app {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules) :
    (Scheme.Modules.pullbackComp (𝟙 X) f).inv.app F ≫
        (Scheme.Modules.pullbackId X).hom.app ((Scheme.Modules.pullback f).obj F) =
      (Scheme.Modules.pullbackCongr (Category.id_comp f)).hom.app F := by
  have p := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality f) F
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Functor.comp_obj, eqToHom_app] at p
  rw [Stacks.Modules.pullbackCongr_hom_app]
  simpa using p

/-- The left unitality coherence of the pullback pseudofunctor, at a module. -/
private theorem pullbackComp_id_right_inv_app {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules) :
    (Scheme.Modules.pullbackComp f (𝟙 Y)).inv.app F ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId Y).hom.app F) =
      (Scheme.Modules.pullbackCongr (Category.comp_id f)).hom.app F := by
  have p := NatTrans.congr_app (Scheme.Modules.pseudofunctor_left_unitality f) F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    Functor.comp_obj, eqToHom_app] at p
  rw [Stacks.Modules.pullbackCongr_hom_app]
  simpa using p

/-- The associativity coherence of the pullback pseudofunctor, with the outer comparison
isomorphism inverted. -/
private theorem pullbackComp_pentagon_inv {X Y Z W : Scheme.{u}} (u : X ⟶ Y) (g : Y ⟶ Z) (v : Z ⟶ W)
    (F : W.Modules)
    (e : (Scheme.Modules.pullback (u ≫ g ≫ v)).obj F =
      (Scheme.Modules.pullback ((u ≫ g) ≫ v)).obj F) :
    (Scheme.Modules.pullbackComp u (g ≫ v)).inv.app F ≫
        (Scheme.Modules.pullback u).map ((Scheme.Modules.pullbackComp g v).inv.app F) ≫
        (Scheme.Modules.pullbackComp u g).hom.app ((Scheme.Modules.pullback v).obj F) =
      eqToHom e ≫ (Scheme.Modules.pullbackComp (u ≫ g) v).inv.app F := by
  rw [← cancel_mono ((Scheme.Modules.pullbackComp (u ≫ g) v).hom.app F)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [Stacks.Modules.pullbackComp_pentagon u g v F]

/-- The right unitality coherence of the pullback pseudofunctor, with the comparison
isomorphisms inverted. -/
private theorem pullbackComp_id_left_hom_app {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules)
    (e : (Scheme.Modules.pullback f).obj F = (Scheme.Modules.pullback (𝟙 X ≫ f)).obj F) :
    (Scheme.Modules.pullbackId X).inv.app ((Scheme.Modules.pullback f).obj F) ≫
        (Scheme.Modules.pullbackComp (𝟙 X) f).hom.app F = eqToHom e := by
  rw [← cancel_epi ((Scheme.Modules.pullbackId X).hom.app
      ((Scheme.Modules.pullback f).obj F)), Iso.hom_inv_id_app_assoc,
    ← cancel_epi ((Scheme.Modules.pullbackComp (𝟙 X) f).inv.app F), Iso.inv_hom_id_app,
    ← Category.assoc, pullbackComp_id_left_inv_app, Stacks.Modules.pullbackCongr_hom_app,
    eqToHom_trans, eqToHom_refl]

/-! ### The two coherences in reindexing form -/

/-- Reindexing twice is reindexing along the composite, up to the canonical transports along
the two bracketings. -/
theorem reindexHom₂_assoc_rev {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {h k : Z ⟶ W}
    {F F' : W.Modules}
    (ψ : (Scheme.Modules.pullback h).obj F ⟶ (Scheme.Modules.pullback k).obj F')
    (e : (Scheme.Modules.pullback (f ≫ g ≫ h)).obj F =
      (Scheme.Modules.pullback ((f ≫ g) ≫ h)).obj F)
    (e' : (Scheme.Modules.pullback ((f ≫ g) ≫ k)).obj F' =
      (Scheme.Modules.pullback (f ≫ g ≫ k)).obj F') :
    reindexHom₂ f (reindexHom₂ g ψ) =
      eqToHom e ≫ reindexHom₂ (f ≫ g) ψ ≫ eqToHom e' := by
  have Ph := pullbackComp_pentagon_inv f g h F e
  have Pk := pullbackComp_pentagon_inv f g k F' e'.symm
  have hPk : (Scheme.Modules.pullbackComp f g).inv.app ((Scheme.Modules.pullback k).obj F') ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g k).hom.app F') ≫
        (Scheme.Modules.pullbackComp f (g ≫ k)).hom.app F' =
      (Scheme.Modules.pullbackComp (f ≫ g) k).hom.app F' ≫ eqToHom e' := by
    rw [← cancel_epi ((Scheme.Modules.pullbackComp f (g ≫ k)).inv.app F' ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g k).inv.app F') ≫
      (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback k).obj F'))]
    conv_rhs => rw [Pk]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
      Iso.inv_hom_id_app]
    simp
  rw [reindexHom₂, reindexHom₂, reindexHom₂, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Functor.comp_map, ← NatIso.naturality_2 (Scheme.Modules.pullbackComp f g) ψ]
  simp only [Category.assoc]
  rw [reassoc_of% Ph, hPk]

/-- Reindexing along an identity morphism is the original morphism, up to the canonical
transports. -/
theorem reindexHom₂_id_left {Y Z : Scheme.{u}} {g h : Y ⟶ Z} {F F' : Z.Modules}
    (ψ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback h).obj F')
    (e : (Scheme.Modules.pullback (𝟙 Y ≫ g)).obj F = (Scheme.Modules.pullback g).obj F)
    (e' : (Scheme.Modules.pullback h).obj F' = (Scheme.Modules.pullback (𝟙 Y ≫ h)).obj F') :
    reindexHom₂ (𝟙 Y) ψ = eqToHom e ≫ ψ ≫ eqToHom e' := by
  have hU := pullbackComp_id_left_inv_app g F
  have hU' := pullbackComp_id_left_hom_app h F' e'
  rw [Stacks.Modules.pullbackCongr_hom_app] at hU
  rw [reindexHom₂, (NatIso.naturality_2 (Scheme.Modules.pullbackId Y) ψ).symm]
  simp only [Category.assoc, Functor.id_map]
  rw [← Category.assoc, hU, hU']

/-- Reindexing along an identity morphism, with the transports written as comparisons of
pullbacks along equal morphisms. -/
theorem reindexHom₂_id_left' {Y Z : Scheme.{u}} {g h : Y ⟶ Z} {F F' : Z.Modules}
    (ψ : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback h).obj F') :
    reindexHom₂ (𝟙 Y) ψ =
      (Scheme.Modules.pullbackCongr (Category.id_comp g)).hom.app F ≫ ψ ≫
        (Scheme.Modules.pullbackCongr (Category.id_comp h).symm).hom.app F' := by
  rw [Stacks.Modules.pullbackCongr_hom_app, Stacks.Modules.pullbackCongr_hom_app]
  exact reindexHom₂_id_left ψ _ _

/-- Reindexing twice is reindexing along the composite, with the transports written as
comparisons of pullbacks along equal morphisms. -/
theorem reindexHom₂_assoc_rev' {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {h k : Z ⟶ W}
    {F F' : W.Modules}
    (ψ : (Scheme.Modules.pullback h).obj F ⟶ (Scheme.Modules.pullback k).obj F') :
    reindexHom₂ f (reindexHom₂ g ψ) =
      (Scheme.Modules.pullbackCongr (Category.assoc f g h).symm).hom.app F ≫
        reindexHom₂ (f ≫ g) ψ ≫
        (Scheme.Modules.pullbackCongr (Category.assoc f g k)).hom.app F' := by
  rw [Stacks.Modules.pullbackCongr_hom_app, Stacks.Modules.pullbackCongr_hom_app]
  exact reindexHom₂_assoc_rev f g ψ _ _

/-- Reindexing along a composite is reindexing twice, with the transports written as
comparisons of pullbacks along equal morphisms. -/
theorem reindexHom₂_assoc' {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {h k : Z ⟶ W}
    {F F' : W.Modules}
    (ψ : (Scheme.Modules.pullback h).obj F ⟶ (Scheme.Modules.pullback k).obj F') :
    reindexHom₂ (f ≫ g) ψ =
      (Scheme.Modules.pullbackCongr (Category.assoc f g h)).hom.app F ≫
        reindexHom₂ f (reindexHom₂ g ψ) ≫
        (Scheme.Modules.pullbackCongr (Category.assoc f g k).symm).hom.app F' := by
  rw [reindexHom₂_assoc_rev']
  simp [Stacks.Modules.pullbackCongr_hom_app]

/-- The left unitality coherence with the comparison isomorphisms inverted. -/
private theorem pullbackComp_id_right_hom_app {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules)
    (e : (Scheme.Modules.pullback f).obj F = (Scheme.Modules.pullback (f ≫ 𝟙 Y)).obj F) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId Y).inv.app F) ≫
      (Scheme.Modules.pullbackComp f (𝟙 Y)).hom.app F = eqToHom e := by
  rw [← cancel_epi ((Scheme.Modules.pullbackComp f (𝟙 Y)).inv.app F ≫
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackId Y).hom.app F))]
  conv_rhs => rw [pullbackComp_id_right_inv_app, Stacks.Modules.pullbackCongr_hom_app]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  rw [CategoryTheory.Functor.map_id (Scheme.Modules.pullback f)
    ((Scheme.Modules.pullback (𝟙 Y)).obj F)]
  simp only [Category.id_comp, Iso.inv_hom_id_app, eqToHom_trans, eqToHom_refl]

/-- The canonical identification of `q^*a^*F` with `q^*F`, for a morphism `a` equal to the
identity, written out. -/
private theorem pullbackComp_id_chain_inv {X Y : Scheme.{u}} (q : X ⟶ Y) {a : Y ⟶ Y} (ha : a = 𝟙 Y)
    (F : Y.Modules)
    (e : (Scheme.Modules.pullback (q ≫ a)).obj F = (Scheme.Modules.pullback q).obj F) :
    (Scheme.Modules.pullbackComp q a).inv.app F ≫
        (Scheme.Modules.pullback q).map ((Scheme.Modules.pullbackCongr ha).hom.app F) ≫
        (Scheme.Modules.pullback q).map ((Scheme.Modules.pullbackId Y).hom.app F) =
      eqToHom e := by
  subst ha
  rw [Stacks.Modules.pullbackCongr_hom_app]
  simp only [eqToHom_refl]
  rw [← Functor.map_comp, Category.id_comp, pullbackComp_id_right_inv_app,
    Stacks.Modules.pullbackCongr_hom_app]

/-- The same identification, inverted. -/
private theorem pullbackComp_id_chain_hom {X Y : Scheme.{u}} (q : X ⟶ Y) {a : Y ⟶ Y} (ha : a = 𝟙 Y)
    (F : Y.Modules)
    (e : (Scheme.Modules.pullback q).obj F = (Scheme.Modules.pullback (q ≫ a)).obj F) :
    (Scheme.Modules.pullback q).map ((Scheme.Modules.pullbackId Y).inv.app F) ≫
        (Scheme.Modules.pullback q).map ((Scheme.Modules.pullbackCongr ha.symm).hom.app F) ≫
        (Scheme.Modules.pullbackComp q a).hom.app F = eqToHom e := by
  calc (Scheme.Modules.pullback q).map ((Scheme.Modules.pullbackId Y).inv.app F) ≫
          (Scheme.Modules.pullback q).map
            ((Scheme.Modules.pullbackCongr ha.symm).hom.app F) ≫
          (Scheme.Modules.pullbackComp q a).hom.app F
      = ((Scheme.Modules.pullback q).map ((Scheme.Modules.pullbackId Y).inv.app F) ≫
            (Scheme.Modules.pullbackComp q (𝟙 Y)).hom.app F) ≫
          ((Scheme.Modules.pullbackComp q (𝟙 Y)).inv.app F ≫
            (Scheme.Modules.pullback q).map
              ((Scheme.Modules.pullbackCongr ha.symm).hom.app F) ≫
            (Scheme.Modules.pullbackComp q a).hom.app F) := by
        simp
    _ = eqToHom e := by
        rw [pullbackComp_id_right_hom_app q F (by rw [Category.comp_id]),
          Stacks.Groupoids.pullbackComp_congr_app, Stacks.Modules.pullbackCongr_hom_app,
          eqToHom_trans]

/-! ### The identity section and restriction along it -/

section Groupoid

open GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- The section of the scheme of composable arrows pairing the identity arrow at the target of
an arrow with the arrow itself.  Its composite is the arrow again. -/
noncomputable def targetIdentitySection : G.arrows ⟶ pullback G.source G.target :=
  pullback.lift (G.target ≫ G.identity) (𝟙 G.arrows)
    (by rw [Category.assoc, G.source_identity, Category.comp_id, Category.id_comp])

/-- The first component of `targetIdentitySection` is the identity arrow at the target. -/
theorem targetIdentitySection_fst :
    targetIdentitySection G ≫ pullback.fst G.source G.target = G.target ≫ G.identity :=
  pullback.lift_fst _ _ _

/-- The second component of `targetIdentitySection` is the arrow itself. -/
theorem targetIdentitySection_snd :
    targetIdentitySection G ≫ pullback.snd G.source G.target = 𝟙 G.arrows :=
  pullback.lift_snd _ _ _

/-- Precomposing an arrow with the identity arrow at its target gives the arrow back. -/
theorem targetIdentitySection_comp : targetIdentitySection G ≫ G.comp = 𝟙 G.arrows := by
  have hw : ((𝟙 G.arrows) ≫ G.target ≫ G.identity) ≫ G.source = (𝟙 G.arrows) ≫ G.target := by
    rw [Category.id_comp, Category.id_comp, Category.assoc, G.source_identity, Category.comp_id]
  have h := G.left_identity G.arrows (𝟙 G.arrows) hw
  have hlift : pullback.lift ((𝟙 G.arrows) ≫ G.target ≫ G.identity) (𝟙 G.arrows) hw =
      targetIdentitySection G := by
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, targetIdentitySection, pullback.lift_fst, Category.id_comp]
    · rw [pullback.lift_snd, targetIdentitySection, pullback.lift_snd]
  rw [← hlift]
  exact h

/-- `targetIdentitySection_fst` on underlying schemes. -/
theorem targetIdentitySection_fst_left :
    (targetIdentitySection G).left ≫ (pullback.fst G.source G.target).left =
      G.target.left ≫ G.identity.left := by
  rw [← Over.comp_left, targetIdentitySection_fst, Over.comp_left]

/-- `targetIdentitySection_snd` on underlying schemes. -/
theorem targetIdentitySection_snd_left :
    (targetIdentitySection G).left ≫ (pullback.snd G.source G.target).left =
      𝟙 G.arrows.left := by
  rw [← Over.comp_left, targetIdentitySection_snd, Over.id_left]

/-- `targetIdentitySection_comp` on underlying schemes. -/
theorem targetIdentitySection_comp_left :
    (targetIdentitySection G).left ≫ G.comp.left = 𝟙 G.arrows.left := by
  rw [← Over.comp_left, targetIdentitySection_comp, Over.id_left]

/-- The restriction of a morphism `t^*F ⟶ t^*F'` along the identity section, read through the
canonical identification of `e^*t^*` with the identity functor. -/
noncomputable def identityRestrictTarget {F F' : G.objects.left.Modules}
    (v : (Scheme.Modules.pullback G.target.left).obj F ⟶
      (Scheme.Modules.pullback G.target.left).obj F') : F ⟶ F' :=
  (Scheme.Modules.pullbackId G.objects.left).inv.app F ≫
    (Scheme.Modules.pullbackCongr (identity_left_comp_target_left G).symm).hom.app F ≫
    reindexHom₂ G.identity.left v ≫
    (Scheme.Modules.pullbackCongr (identity_left_comp_target_left G)).hom.app F' ≫
    (Scheme.Modules.pullbackId G.objects.left).hom.app F'

/-- The restriction of a morphism `s^*F ⟶ t^*F'` along the identity section, read through the
canonical identifications of `e^*s^*` and of `e^*t^*` with the identity functor. -/
noncomputable def identityRestrict {F F' : G.objects.left.Modules}
    (ψ : (Scheme.Modules.pullback G.source.left).obj F ⟶
      (Scheme.Modules.pullback G.target.left).obj F') : F ⟶ F' :=
  (Scheme.Modules.pullbackId G.objects.left).inv.app F ≫
    (Scheme.Modules.pullbackCongr (identity_left_comp_source_left G).symm).hom.app F ≫
    reindexHom₂ G.identity.left ψ ≫
    (Scheme.Modules.pullbackCongr (identity_left_comp_target_left G)).hom.app F' ≫
    (Scheme.Modules.pullbackId G.objects.left).hom.app F'

/-- Restricting the inverse image along the target of a morphism of modules gives the morphism
back. -/
@[simp]
theorem identityRestrictTarget_pullback_map {F F' : G.objects.left.Modules} (f : F ⟶ F') :
    identityRestrictTarget G ((Scheme.Modules.pullback G.target.left).map f) = f := by
  have hnat := (Scheme.Modules.pullbackCongr
    (identity_left_comp_target_left G)).hom.naturality f
  have hid := (Scheme.Modules.pullbackId G.objects.left).hom.naturality f
  simp only [Functor.id_map] at hid
  rw [identityRestrictTarget, reindexHom₂_pullback_map, reassoc_of% hnat,
    Stacks.Modules.pullbackCongr_hom_app, Stacks.Modules.pullbackCongr_hom_app]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [hid, Iso.inv_hom_id_app_assoc]

/-- **The identity condition in restriction form.**  Restricting `α` followed by a morphism
`s^*F ⟶ t^*F'` along the identity section is the restriction of the morphism alone. -/
theorem identityRestrictTarget_alpha_comp (M : QuasicoherentModule G)
    {F' : G.objects.left.Modules}
    (ψ : (Scheme.Modules.pullback G.source.left).obj M.module ⟶
      (Scheme.Modules.pullback G.target.left).obj F') :
    identityRestrictTarget G (M.alpha ≫ ψ) = identityRestrict G ψ := by
  have hsplit : identityRestrictTarget G (M.alpha ≫ ψ) =
      identityDescent G M.alpha ≫ identityRestrict G ψ := by
    rw [identityRestrictTarget, identityRestrict, identityDescent, reindexHom₂_comp,
      reindexHom₂_eq_reindexHom]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
      Stacks.Modules.pullbackCongr_hom_app, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
  rw [hsplit, M.identity, Category.id_comp]

/-- Pulling the restriction of `ψ` along the identity section back along the target is the
twofold reindexing of `ψ`, along the target and then along the identity section. -/
theorem pullback_map_identityRestrict {F F' : G.objects.left.Modules}
    (ψ : (Scheme.Modules.pullback G.source.left).obj F ⟶
      (Scheme.Modules.pullback G.target.left).obj F')
    (e₁ : (Scheme.Modules.pullback G.target.left).obj F =
      (Scheme.Modules.pullback
        (G.target.left ≫ G.identity.left ≫ G.source.left)).obj F)
    (e₂ : (Scheme.Modules.pullback
        (G.target.left ≫ G.identity.left ≫ G.target.left)).obj F' =
      (Scheme.Modules.pullback G.target.left).obj F') :
    (Scheme.Modules.pullback G.target.left).map (identityRestrict G ψ) =
      eqToHom e₁ ≫ reindexHom₂ G.target.left (reindexHom₂ G.identity.left ψ) ≫ eqToHom e₂ := by
  have hP : (Scheme.Modules.pullback G.target.left).map
        ((Scheme.Modules.pullbackId G.objects.left).inv.app F) ≫
      (Scheme.Modules.pullback G.target.left).map
        ((Scheme.Modules.pullbackCongr (identity_left_comp_source_left G).symm).hom.app F) =
      eqToHom e₁ ≫ (Scheme.Modules.pullbackComp G.target.left
        (G.identity.left ≫ G.source.left)).inv.app F := by
    rw [← cancel_mono ((Scheme.Modules.pullbackComp G.target.left
      (G.identity.left ≫ G.source.left)).hom.app F)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    exact pullbackComp_id_chain_hom G.target.left (identity_left_comp_source_left G) F e₁
  have hQ : (Scheme.Modules.pullback G.target.left).map
        ((Scheme.Modules.pullbackCongr (identity_left_comp_target_left G)).hom.app F') ≫
      (Scheme.Modules.pullback G.target.left).map
        ((Scheme.Modules.pullbackId G.objects.left).hom.app F') =
      (Scheme.Modules.pullbackComp G.target.left
        (G.identity.left ≫ G.target.left)).hom.app F' ≫ eqToHom e₂ := by
    rw [← cancel_epi ((Scheme.Modules.pullbackComp G.target.left
      (G.identity.left ≫ G.target.left)).inv.app F')]
    simp only [Iso.inv_hom_id_app_assoc]
    exact pullbackComp_id_chain_inv G.target.left (identity_left_comp_target_left G) F' e₂
  rw [identityRestrict]
  simp only [reindexHom₂, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hP, hQ]

/-- **The forward map of the hom-set bijection of Tag 07TR.**  A morphism `𝓕 ⟶ 𝒢` of modules on
the object scheme is sent to the adjunct along the source of the inverse descent morphism
followed by `t^*` of it. -/
noncomputable def transpose (M : QuasicoherentModule G) (𝒢 : G.objects.left.Modules)
    (f : M.module ⟶ 𝒢) :
    M.module ⟶ (Scheme.Modules.pushforward G.source.left).obj
      ((Scheme.Modules.pullback G.target.left).obj 𝒢) :=
  (Scheme.Modules.pullbackPushforwardAdjunction G.source.left).homEquiv M.module
    ((Scheme.Modules.pullback G.target.left).obj 𝒢)
    (inv M.alpha ≫ (Scheme.Modules.pullback G.target.left).map f)

/-- **The inverse map of the hom-set bijection of Tag 07TR.**  A morphism
`𝓕 ⟶ s_* t^* 𝒢` is sent to the restriction along the identity section of the descent morphism
followed by its inverse adjunct along the source. -/
noncomputable def untranspose (M : QuasicoherentModule G) (𝒢 : G.objects.left.Modules)
    (g : M.module ⟶ (Scheme.Modules.pushforward G.source.left).obj
      ((Scheme.Modules.pullback G.target.left).obj 𝒢)) : M.module ⟶ 𝒢 :=
  identityRestrictTarget G (M.alpha ≫
    ((Scheme.Modules.pullbackPushforwardAdjunction G.source.left).homEquiv M.module
      ((Scheme.Modules.pullback G.target.left).obj 𝒢)).symm g)

/-- **The first round trip.**  The inverse map undoes the forward map.  Only the invertibility
of the descent morphism and the identification `e^*t^* ≅ 𝟭` are used. -/
theorem untranspose_transpose (M : QuasicoherentModule G) (𝒢 : G.objects.left.Modules)
    (f : M.module ⟶ 𝒢) : untranspose G M 𝒢 (transpose G M 𝒢 f) = f := by
  rw [untranspose, transpose, Equiv.symm_apply_apply, IsIso.hom_inv_id_assoc,
    identityRestrictTarget_pullback_map]

end Groupoid

end Stacks.Groupoids.GroupoidScheme

end
