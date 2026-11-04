module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Equivariant
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.StabilizerBaseChangeMorphism
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantOpenSubgroupoid
import all StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Equivariant

/-!
# Twisted base change of a groupoid scheme

Let `G = (U, R, s, t, c)` be a groupoid scheme over `S`, let `p : U' ⟶ U` and `q : U' ⟶ V` be two
morphisms which are *jointly monic*, and suppose that for every point `u'` of `U'` and every arrow
`r` of `G` with target `p(u')` there is a point of `U'` over the source of `r` with the same image
in `V`. This is the situation of a base change `U' = U ×_Y V` along a morphism `V ⟶ Y` to an
algebraic space receiving an `R`-invariant morphism `U ⟶ Y`: the point is `(s(r), q(u'))`, and
the arrows of the base-changed groupoid are the pairs `(u', r)`, so that
`R' = U' ×_{U, t} R = U' ×_{U, s} R` and the stabilizer of `R'` is the base change of the
stabilizer of `R`.

This file packages such data as `AlgebraicGeometry.GroupoidScheme.TwistedBaseChange`, turns it into
an equivariant scheme for `G` (so into a groupoid scheme cartesian over `G`, Stacks 0APE), and
proves that the morphism to `G` has cartesian source, target and stabilizer squares. It also shows
that the restriction to an invariant open keeps the three squares cartesian, which is the shape of
the hypotheses of Stacks 0DT9.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.TwistedBaseChange`: the data above.
* `AlgebraicGeometry.GroupoidScheme.TwistedBaseChange.groupoid` and
  `AlgebraicGeometry.GroupoidScheme.TwistedBaseChange.hom`: the base-changed groupoid and its
  morphism to `G`.

## Main results

* `AlgebraicGeometry.GroupoidScheme.TwistedBaseChange.isPullback_source`,
  `AlgebraicGeometry.GroupoidScheme.TwistedBaseChange.isPullback_target` and
  `AlgebraicGeometry.GroupoidScheme.TwistedBaseChange.isPullback_stabilizer`: the three cartesian
  squares.
* `AlgebraicGeometry.GroupoidScheme.isPullback_restrictInvariantOpenHom_source` and
  `AlgebraicGeometry.GroupoidScheme.isPullback_restrictInvariantOpenHom_target`: the restriction to
  an invariant open is cartesian.
-/

universe u

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

noncomputable section

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}}

/-- **Twisted base change data for a groupoid scheme `G`.** A scheme `U'` over `S` with two jointly
monic morphisms `p : U' ⟶ U` and `q : U' ⟶ V`, and an action of the arrows of `G`: a point `u'`
over the target of an arrow `r` is carried to a point over the source of `r` with the same image
in `V`. -/
structure TwistedBaseChange (G : GroupoidScheme S) where
  /-- The object scheme `U'` of the base change. -/
  obj : Over S
  /-- The auxiliary scheme `V`. -/
  aux : Over S
  /-- The projection to the object scheme of `G`. -/
  proj : obj ⟶ G.objects
  /-- The projection to the auxiliary scheme. -/
  toAux : obj ⟶ aux
  /-- The two projections are jointly monic. -/
  ext : ∀ {T : Over S} (a b : T ⟶ obj), a ≫ proj = b ≫ proj → a ≫ toAux = b ≫ toAux → a = b
  /-- The action of an arrow on a point over its target. -/
  act : pullback proj G.target ⟶ obj
  /-- The image in `U` of the action of an arrow is its source. -/
  act_proj : act ≫ proj = pullback.snd proj G.target ≫ G.source
  /-- The action of an arrow preserves the image in `V`. -/
  act_toAux : act ≫ toAux = pullback.fst proj G.target ≫ toAux

namespace TwistedBaseChange

variable {G : GroupoidScheme S} (D : TwistedBaseChange G)

attribute [reassoc] act_proj act_toAux

/-- The inverse action: a point over the source of an arrow, carried to a point over its target
by the action of the inverse arrow. -/
def invAct : pullback G.source D.proj ⟶ pullback D.proj G.target :=
  pullback.lift
    (pullback.lift (pullback.snd G.source D.proj) (pullback.fst G.source D.proj ≫ G.inverse)
      (by rw [Category.assoc, G.target_inverse, pullback.condition]) ≫ D.act)
    (pullback.fst G.source D.proj)
    (by rw [Category.assoc, D.act_proj, pullback.lift_snd_assoc, Category.assoc,
      G.source_inverse])

/-- The descent isomorphism `U' ×_{U, t} R ≅ R ×_{s, U} U'` of the twisted base change. -/
@[simps]
def descentIso : pullback D.proj G.target ≅ pullback G.source D.proj where
  hom := pullback.lift (pullback.snd D.proj G.target) D.act D.act_proj.symm
  inv := D.invAct
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [invAct, Category.assoc, pullback.lift_fst, Category.id_comp]
      apply D.ext
      · simp only [Category.assoc, D.act_proj, pullback.lift_snd_assoc, pullback.lift_fst_assoc,
          G.source_inverse]
        exact pullback.condition.symm
      · simp only [Category.assoc, D.act_toAux, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    · simp only [invAct, Category.assoc, pullback.lift_snd, pullback.lift_fst, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [invAct, Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
      apply D.ext
      · simp only [invAct, Category.assoc, D.act_proj, pullback.lift_snd_assoc]
        exact pullback.condition
      · simp only [invAct, Category.assoc, D.act_toAux, pullback.lift_fst_assoc]

/-- The second component of the descent isomorphism is the action. -/
theorem descentIso_hom_snd :
    D.descentIso.hom ≫ pullback.snd G.source D.proj = D.act := by
  rw [descentIso_hom, pullback.lift_snd]

/-- The image in `U` of the action of an arrow is its source. -/
theorem lift_descent_proj {T : Over S} (v : T ⟶ D.obj) (f : T ⟶ G.arrows)
    (w : v ≫ D.proj = f ≫ G.target) :
    (pullback.lift v f w ≫ D.descentIso.hom ≫ pullback.snd G.source D.proj) ≫ D.proj =
      f ≫ G.source := by
  rw [descentIso_hom_snd, Category.assoc, D.act_proj, pullback.lift_snd_assoc]

/-- The image in `V` of the action of an arrow is that of the point acted on. -/
theorem lift_descent_toAux {T : Over S} (v : T ⟶ D.obj) (f : T ⟶ G.arrows)
    (w : v ≫ D.proj = f ≫ G.target) :
    (pullback.lift v f w ≫ D.descentIso.hom ≫ pullback.snd G.source D.proj) ≫ D.toAux =
      v ≫ D.toAux := by
  rw [descentIso_hom_snd, Category.assoc, D.act_toAux, pullback.lift_fst_assoc]

/-- **The equivariant scheme of a twisted base change.** -/
def equivariantScheme : EquivariantScheme G where
  obj := Over.mk D.proj
  descentIso := D.descentIso
  descentIso_over := pullback.lift_fst _ _ _
  identity := by
    intro T v
    apply D.ext
    · refine (D.lift_descent_proj v (v ≫ D.proj ≫ G.identity) _).trans ?_
      simp [G.source_identity]
    · exact D.lift_descent_toAux v (v ≫ D.proj ≫ G.identity) _
  cocycle := by
    intro T v f g wvf wfg
    apply D.ext
    · refine (D.lift_descent_proj _ g _).trans
        ((D.lift_descent_proj v (G.compose f g wfg) _).trans ?_).symm
      rw [GroupoidScheme.compose, Category.assoc, G.source_comp, pullback.lift_snd_assoc]
    · exact (D.lift_descent_toAux _ g _).trans ((D.lift_descent_toAux v f wvf).trans
        (D.lift_descent_toAux v (G.compose f g wfg) _).symm)

/-- **The groupoid scheme of a twisted base change**: objects `U'`, arrows `U' ×_{U, t} R`. -/
abbrev groupoid : GroupoidScheme S := equivariantActionGroupoid D.equivariantScheme

/-- The objects of the twisted base change groupoid are `U'`. -/
theorem groupoid_objects : D.groupoid.objects = D.obj := rfl

/-- The arrows of the twisted base change groupoid are `U' ×_{U, t} R`. -/
theorem groupoid_arrows : D.groupoid.arrows = pullback D.proj G.target := rfl

/-- The target of the twisted base change groupoid is the first projection. -/
theorem groupoid_target : D.groupoid.target = pullback.fst D.proj G.target := rfl

/-- The source of the twisted base change groupoid is the action. -/
theorem groupoid_source : D.groupoid.source = D.act := by
  show pullback.lift (pullback.fst D.proj G.target) (pullback.snd D.proj G.target) _ ≫
    D.descentIso.hom ≫ pullback.snd G.source D.proj = D.act
  rw [descentIso_hom_snd, pullback.lift_fst_snd, Category.id_comp]

end TwistedBaseChange

end AlgebraicGeometry.GroupoidScheme

end

end

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

noncomputable section

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}}

namespace TwistedBaseChange

variable {G : GroupoidScheme S} (D : TwistedBaseChange G)

/-- The compatibility with composition of the morphism from the twisted base change to `G`. -/
theorem hom_map_comp (T : Over S) (f g : T ⟶ D.groupoid.arrows)
    (w : f ≫ D.groupoid.source = g ≫ D.groupoid.target)
    (w' : (f ≫ pullback.snd D.proj G.target) ≫ G.source =
      (g ≫ pullback.snd D.proj G.target) ≫ G.target) :
    D.groupoid.compose f g w ≫ pullback.snd D.proj G.target =
      G.compose (f ≫ pullback.snd D.proj G.target) (g ≫ pullback.snd D.proj G.target) w' :=
  (equivariantActionGroupoidHom D.equivariantScheme).map_comp T f g w w'

/-- **The morphism from the twisted base change to `G`**: the projection on objects and the
second projection `U' ×_{U, t} R ⟶ R` on arrows. -/
def hom : GroupoidScheme.Hom D.groupoid G where
  mapObjects := D.proj
  mapArrows := pullback.snd D.proj G.target
  map_source := (D.equivariantScheme.action_comp_hom
      (pullback.fst D.proj G.target) (pullback.snd D.proj G.target) pullback.condition).symm
  map_target := pullback.condition.symm
  map_identity := (equivariantActionArrowIdentity_base D.equivariantScheme).symm
  map_comp := D.hom_map_comp

/-- On objects, the morphism to `G` is the projection `U' ⟶ U`. -/
theorem hom_mapObjects : D.hom.mapObjects = D.proj := rfl

/-- On arrows, the morphism to `G` is the second projection `U' ×_{U, t} R ⟶ R`. -/
theorem hom_mapArrows : D.hom.mapArrows = pullback.snd D.proj G.target := rfl

/-- The source square of the twisted base change is cartesian. -/
theorem isPullback_source :
    IsPullback D.hom.mapArrows.left D.groupoid.source.left G.source.left D.hom.mapObjects.left :=
  equivariantActionGroupoidHom_cartesian D.equivariantScheme

/-- The projection to the auxiliary scheme, read on the objects of the twisted base change. -/
abbrev toAuxG : D.groupoid.objects ⟶ D.aux := D.toAux

/-- The source and target of an arrow of the twisted base change have the same image in `V`. -/
theorem source_toAux : D.groupoid.source ≫ D.toAuxG = D.groupoid.target ≫ D.toAuxG := by
  rw [groupoid_source]
  exact D.act_toAux

/-- Joint monicity, read on the objects of the twisted base change. -/
theorem ext' {T : Over S} (a b : T ⟶ D.groupoid.objects)
    (h₁ : a ≫ D.hom.mapObjects = b ≫ D.hom.mapObjects) (h₂ : a ≫ D.toAuxG = b ≫ D.toAuxG) :
    a = b :=
  D.ext a b h₁ h₂

/-- The target square of the twisted base change is cartesian. -/
theorem isPullback_target :
    IsPullback D.hom.mapArrows.left D.groupoid.target.left G.target.left D.hom.mapObjects.left :=
  (IsPullback.of_isLimit_cone (isLimitOfPreserves (Over.forget S)
    (limit.isLimit (cospan D.proj G.target)))).flip

/-- **An arrow of the twisted base change whose image has equal source and target has equal source
and target**: the two points of `U'` have the same images in `U` and in `V`. -/
theorem source_eq_target {T : Scheme.{u}} (r : T ⟶ D.groupoid.arrows.left)
    (hr : (r ≫ D.hom.mapArrows.left) ≫ G.source.left = (r ≫ D.hom.mapArrows.left) ≫ G.target.left) :
    r ≫ D.groupoid.source.left = r ≫ D.groupoid.target.left := by
  let r' : (Over.mk (r ≫ D.groupoid.arrows.hom) : Over S) ⟶ D.groupoid.arrows := Over.homMk r
  have hs := D.hom.map_source
  have ht := D.hom.map_target
  have h := D.ext' (r' ≫ D.groupoid.source) (r' ≫ D.groupoid.target) ?_ ?_
  · exact congrArg Over.Hom.left h
  · rw [Category.assoc, Category.assoc, ← hs, ← ht]
    ext
    simpa [r'] using hr
  · rw [Category.assoc, Category.assoc, D.source_toAux]

/-- The stabilizer square of the twisted base change is cartesian. -/
theorem isPullback_stabilizer :
    IsPullback (stabilizerMap D.hom).left (stabilizer D.groupoid).hom (stabilizer G).hom
      D.hom.mapObjects.left :=
  isPullback_stabilizerMap D.hom D.isPullback_target fun r hr => D.source_eq_target r hr

end TwistedBaseChange

/-! ### Restriction to an invariant open -/

section Restriction

/-- A square of open immersions over a morphism, with the open upstairs the preimage of the open
downstairs, is cartesian. -/
theorem isPullback_opens_ι_of_eq_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (B : Y.Opens)
    (A : X.Opens) (hA : A = f ⁻¹ᵁ B) (g : A.toScheme ⟶ B.toScheme) (hg : g ≫ B.ι = A.ι ≫ f) :
    IsPullback A.ι g f B.ι := by
  subst hA
  have : g = f ∣_ B := by
    rw [← cancel_mono B.ι, hg, morphismRestrict_ι]
  subst this
  exact (isPullback_morphismRestrict f B).flip

variable (H : GroupoidScheme S) (W : H.objects.left.Opens) (hW : IsInvariantOpen H W)

/-- The source square of the restriction of a groupoid scheme to an invariant open is cartesian. -/
theorem isPullback_restrictInvariantOpenHom_source :
    IsPullback (restrictInvariantOpenHom H W hW).mapArrows.left
      (restrictInvariantOpen H W hW).source.left H.source.left
      (restrictInvariantOpenHom H W hW).mapObjects.left :=
  isPullback_opens_ι_of_eq_preimage H.source.left W (invariantArrows H W) rfl _
    (congrArg Over.Hom.left (invariantSource_ι H W))

/-- The target square of the restriction of a groupoid scheme to an invariant open is cartesian. -/
theorem isPullback_restrictInvariantOpenHom_target :
    IsPullback (restrictInvariantOpenHom H W hW).mapArrows.left
      (restrictInvariantOpen H W hW).target.left H.target.left
      (restrictInvariantOpenHom H W hW).mapObjects.left :=
  isPullback_opens_ι_of_eq_preimage H.target.left W (invariantArrows H W)
    (TopologicalSpace.Opens.ext (Set.ext fun r => mem_invariantArrows_iff_target H W hW r)) _
    (congrArg Over.Hom.left (invariantTarget_ι H W hW))

end Restriction

end AlgebraicGeometry.GroupoidScheme

end

end
