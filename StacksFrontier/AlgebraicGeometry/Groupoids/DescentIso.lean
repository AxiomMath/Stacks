module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback

/-!
# The descent morphism of a groupoid module is an isomorphism

For a quasi-coherent module on a groupoid scheme, the morphism comparing its pullbacks along
the target and the source map is automatically invertible.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.QuasicoherentModule.descentInverse` is the inverse of the
  descent morphism, namely its reindexing along the inverse map of the groupoid.
* `Stacks.Groupoids.GroupoidScheme.QuasicoherentModule.rightInverseSection` and
  `Stacks.Groupoids.GroupoidScheme.QuasicoherentModule.leftInverseSection` are the two
  sections of the scheme of composable arrows which pair an arrow with its inverse.

## Main results

* `Stacks.Groupoids.GroupoidScheme.QuasicoherentModule.alpha_isIso` states that the descent
  morphism of a quasi-coherent module on a groupoid scheme is an isomorphism.
* `Stacks.Groupoids.reindexHom_congr`, `Stacks.Groupoids.reindexHom_congr_source`,
  `Stacks.Groupoids.reindexHom_id_left` and `Stacks.Groupoids.reindexHom_assoc` extend the
  `reindexHom` calculus to transport along equalities of morphisms and to iterated reindexing.
* `Stacks.Groupoids.GroupoidScheme.reindexHom_successiveDescent` reindexes the
  successive-descent morphism through the reindexings along the two projections, and
  `Stacks.Groupoids.GroupoidScheme.QuasicoherentModule.reindexed_cocycle_right` and
  `..._left` are the two instances of the cocycle law used to build the inverse.

## Implementation notes

The conclusion is provided as an `IsIso` instance so that the inverse descent morphism and its
canonical inverse identities are directly available to subsequent constructions.

Both inverse identities are obtained from the cocycle law by reindexing it along the section of
the scheme of composable arrows which pairs an arrow with its inverse; the normalization along
the identity section then turns the composite into an identity.  Because pullback of modules is
only a pseudofunctor, each of these steps carries the canonical comparison isomorphisms, which
is what the `reindexHom` calculus below is for.

The comparison isomorphisms are manipulated through
`Stacks.Groupoids.pullbackCongr_hom_app_comp` and its companions rather than by unfolding
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` to `eqToHom`.  Unfolding it forces every
rewrite to be justified by an equality of pullback functors, and the resulting proof terms are
too large to recheck; keeping the equalities at the level of morphisms of schemes avoids that.

## References

* [Stacks Project, Tag 077Q](https://stacks.math.columbia.edu/tag/077Q)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids

/-- Composing the comparisons of pullbacks along `f = g` and along `g = h` gives the
comparison along `f = h`. -/
@[reassoc]
theorem pullbackCongr_hom_app_comp {X Y : Scheme.{u}} {f g h : X ⟶ Y} (p : f = g) (q : g = h)
    (F : Y.Modules) :
    (Scheme.Modules.pullbackCongr p).hom.app F ≫ (Scheme.Modules.pullbackCongr q).hom.app F =
      (Scheme.Modules.pullbackCongr (p.trans q)).hom.app F := by
  subst q p
  simp [Scheme.Modules.pullbackCongr]

/-- The comparison of pullbacks along a reflexive equality is the identity. -/
@[simp]
theorem pullbackCongr_hom_app_self {X Y : Scheme.{u}} {f : X ⟶ Y} (p : f = f)
    (F : Y.Modules) :
    (Scheme.Modules.pullbackCongr p).hom.app F = 𝟙 _ := by
  simp [Scheme.Modules.pullbackCongr]

/-- The inverse of the comparison of pullbacks along `f = g` is the comparison along `g = f`. -/
@[simp]
theorem pullbackCongr_inv_app {X Y : Scheme.{u}} {f g : X ⟶ Y} (p : f = g) (F : Y.Modules) :
    (Scheme.Modules.pullbackCongr p).inv.app F =
      (Scheme.Modules.pullbackCongr p.symm).hom.app F := by
  subst p
  simp [Scheme.Modules.pullbackCongr]

/-- Reindexing the canonical comparison of pullbacks along equal morphisms is again such a
comparison, for the composites. -/
theorem reindexHom_congr {X Y Z : Scheme.{u}} (f : X ⟶ Y) {g h : Y ⟶ Z} (p : g = h)
    (F : Z.Modules) :
    reindexHom f ((Scheme.Modules.pullbackCongr p).hom.app F) =
      (Scheme.Modules.pullbackCongr (congrArg (fun x ↦ f ≫ x) p)).hom.app F := by
  cases p
  simp [reindexHom, Scheme.Modules.pullbackCongr]

/-- Replacing the reindexing morphism by an equal one is the same as conjugating by the
canonical comparisons of pullbacks along the two resulting composites. -/
theorem reindexHom_congr_source {X Y Z : Scheme.{u}} {f f' : X ⟶ Y} (p : f = f')
    {g h : Y ⟶ Z} {F : Z.Modules}
    (α : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback h).obj F) :
    reindexHom f α =
      (Scheme.Modules.pullbackCongr (congrArg (fun x ↦ x ≫ g) p)).hom.app F ≫
        reindexHom f' α ≫
        (Scheme.Modules.pullbackCongr (congrArg (fun x ↦ x ≫ h) p).symm).hom.app F := by
  cases p
  simp [Scheme.Modules.pullbackCongr]

/-- Reindexing along an identity morphism is the original morphism, up to the canonical
comparisons of pullback along `𝟙 ≫ g` with pullback along `g`. -/
theorem reindexHom_id_left {Y Z : Scheme.{u}} {g h : Y ⟶ Z} {F : Z.Modules}
    (α : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback h).obj F) :
    reindexHom (𝟙 Y) α =
      (Scheme.Modules.pullbackCongr (Category.id_comp g)).hom.app F ≫ α ≫
        (Scheme.Modules.pullbackCongr (Category.id_comp h).symm).hom.app F := by
  simp only [reindexHom, Scheme.Modules.pullbackCongr]
  have pg := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality g) F
  have ph := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality h) F
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Functor.comp_obj, eqToHom_app] at pg ph
  let Cg := Scheme.Modules.pullbackComp (𝟙 Y) g
  let Ch := Scheme.Modules.pullbackComp (𝟙 Y) h
  let Ig := (Scheme.Modules.pullbackId Y).app ((Scheme.Modules.pullback g).obj F)
  let Ih := (Scheme.Modules.pullbackId Y).app ((Scheme.Modules.pullback h).obj F)
  let Eg := Scheme.Modules.pullbackCongr (Category.id_comp g)
  let Eh := Scheme.Modules.pullbackCongr (Category.id_comp h)
  have pg' : Cg.inv.app F ≫ Ig.hom = Eg.hom.app F := by
    simpa [Cg, Ig, Eg, Scheme.Modules.pullbackCongr] using pg
  have ph' : Ch.inv.app F ≫ Ih.hom = Eh.hom.app F := by
    simpa [Ch, Ih, Eh, Scheme.Modules.pullbackCongr] using ph
  have hg : Eg.hom.app F ≫ Ig.inv = Cg.inv.app F := (Iso.comp_inv_eq Ig).mpr pg'.symm
  have hh : Ih.hom ≫ (Eh.app F).inv = Ch.hom.app F := by
    refine (Iso.comp_inv_eq (Eh.app F)).mpr ?_
    calc Ih.hom = Ch.hom.app F ≫ Ch.inv.app F ≫ Ih.hom := by simp
      _ = Ch.hom.app F ≫ Eh.hom.app F := by rw [ph']
  change Cg.inv.app F ≫ (Scheme.Modules.pullback (𝟙 Y)).map α ≫ Ch.hom.app F =
    Eg.hom.app F ≫ α ≫ (Eh.app F).inv
  rw [← hg, ← hh]
  simp only [Category.assoc]
  dsimp [Ig, Ih]
  rw [NatTrans.naturality_assoc (Scheme.Modules.pullbackId Y).hom α]
  simp

/-- Reindexing along a composite is the same as reindexing twice, up to the canonical
comparisons of pullback along the reassociated composites. -/
theorem reindexHom_assoc {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {h k : Z ⟶ W}
    {F : W.Modules}
    (α : (Scheme.Modules.pullback h).obj F ⟶ (Scheme.Modules.pullback k).obj F) :
    reindexHom (f ≫ g) α =
      (Scheme.Modules.pullbackCongr (Category.assoc f g h)).hom.app F ≫
        reindexHom f (reindexHom g α) ≫
        (Scheme.Modules.pullbackCongr (Category.assoc f g k).symm).hom.app F := by
  simp only [reindexHom, Scheme.Modules.pullbackCongr]
  have ph := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity f g h) F
  have pk := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity f g k) F
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at ph pk
  simp only [eqToIso.hom]
  rw [← pk]
  simp only [Functor.map_comp, Category.assoc]
  simp only [Iso.hom_inv_id_app_assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  simp only [Functor.associator_hom_app, Category.id_comp] at ph pk ⊢
  simp only [← Category.assoc, Functor.map_comp] at ph pk ⊢
  rw [CategoryTheory.Functor.map_id (Scheme.Modules.pullback f)
    ((Scheme.Modules.pullback k ⋙ Scheme.Modules.pullback g).obj F)]
  simp only [Functor.comp_obj]
  rw [Category.comp_id, ← Functor.comp_map (Scheme.Modules.pullback g)
    (Scheme.Modules.pullback f) α]
  simp only [Category.assoc]
  rw [NatTrans.naturality_assoc (Scheme.Modules.pullbackComp f g).hom α]
  let H := Scheme.Modules.pullbackComp (f ≫ g) h
  let P := (Scheme.Modules.pullbackComp f (g ≫ h)).inv.app F ≫
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app F) ≫
    (Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj F)
  have hp : P ≫ H.hom.app F =
      (Scheme.Modules.pullbackCongr (Category.assoc f g h).symm).hom.app F := by
    simpa [P, H, Scheme.Modules.pullbackCongr] using ph
  have he : (Scheme.Modules.pullbackCongr (Category.assoc f g h)).hom.app F ≫ P =
      H.inv.app F := by
    calc _ = ((Scheme.Modules.pullbackCongr (Category.assoc f g h)).hom.app F ≫ P ≫
          H.hom.app F) ≫ H.inv.app F := by simp
      _ = ((Scheme.Modules.pullbackCongr (Category.assoc f g h)).hom.app F ≫
          (Scheme.Modules.pullbackCongr (Category.assoc f g h).symm).hom.app F) ≫
          H.inv.app F := by rw [hp]
      _ = H.inv.app F := by simp [Scheme.Modules.pullbackCongr]
  rw [← he]
  simp [P, Scheme.Modules.pullbackCongr]

/-- Reindexing twice is the same as reindexing along the composite, up to the canonical
comparisons of pullback along the reassociated composites. -/
theorem reindexHom_assoc_rev {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {h k : Z ⟶ W}
    {F : W.Modules}
    (α : (Scheme.Modules.pullback h).obj F ⟶ (Scheme.Modules.pullback k).obj F) :
    reindexHom f (reindexHom g α) =
      (Scheme.Modules.pullbackCongr (Category.assoc f g h).symm).hom.app F ≫
        reindexHom (f ≫ g) α ≫
        (Scheme.Modules.pullbackCongr (Category.assoc f g k)).hom.app F := by
  rw [reindexHom_assoc]
  simp [pullbackCongr_hom_app_comp, pullbackCongr_hom_app_comp_assoc]

namespace GroupoidScheme

variable {S : Scheme.{u}} {G : GroupoidScheme S}

/-- Reindexing a normalized descent morphism along the identity section is the canonical
comparison of the pullbacks along `identity ≫ target` and `identity ≫ source`. -/
theorem reindexHom_identity (G : GroupoidScheme S) {F : G.objects.left.Modules}
    (α : (Scheme.Modules.pullback G.target.left).obj F ⟶
      (Scheme.Modules.pullback G.source.left).obj F)
    (h : identityDescent G α = 𝟙 F) :
    reindexHom G.identity.left α =
      (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left G.target_identity)).hom.app F ≫
        (Scheme.Modules.pullbackCongr
          (congrArg Over.Hom.left G.source_identity).symm).hom.app F := by
  dsimp only [identityDescent] at h
  let B := Scheme.Modules.pullbackCongr (congrArg Over.Hom.left G.target_identity).symm
  let D := Scheme.Modules.pullbackCongr (congrArg Over.Hom.left G.source_identity)
  have h' : B.hom.app F ≫ reindexHom G.identity.left α ≫ D.hom.app F = 𝟙 _ := by
    simpa [B, D] using congrArg (fun z ↦ (Scheme.Modules.pullbackId G.objects.left).hom.app F ≫
      z ≫ (Scheme.Modules.pullbackId G.objects.left).inv.app F) h
  change reindexHom G.identity.left α = B.inv.app F ≫ D.inv.app F
  calc reindexHom G.identity.left α
      = B.inv.app F ≫ (B.hom.app F ≫ reindexHom G.identity.left α ≫ D.hom.app F) ≫
        D.inv.app F := by simp
    _ = B.inv.app F ≫ D.inv.app F := by
      rw [h']
      simp

/-- Reindexing a normalized descent morphism along a morphism to the objects followed by the
identity section is the canonical comparison of the two resulting pullbacks. -/
theorem reindexHom_comp_identity {X : Scheme.{u}} (G : GroupoidScheme S)
    (f : X ⟶ G.objects.left) {F : G.objects.left.Modules}
    (α : (Scheme.Modules.pullback G.target.left).obj F ⟶
      (Scheme.Modules.pullback G.source.left).obj F)
    (h : identityDescent G α = 𝟙 F) :
    reindexHom (f ≫ G.identity.left) α =
      (Scheme.Modules.pullbackCongr (show (f ≫ G.identity.left) ≫ G.target.left =
        (f ≫ G.identity.left) ≫ G.source.left from by
        rw [Category.assoc, Category.assoc, identity_left_comp_source_left G,
          identity_left_comp_target_left G])).hom.app F := by
  rw [reindexHom_assoc, reindexHom_identity G α h, reindexHom_comp, reindexHom_congr,
    reindexHom_congr]
  simp [pullbackCongr_hom_app_comp]

/-- Reindexing the successive-descent morphism along a morphism into the scheme of composable
arrows, expressed through the reindexings along the two projections.  The three equalities are
the comparisons of pullbacks that the pseudofunctoriality of pullback forces into the
statement; they are hypotheses so that any proof of them may be supplied. -/
theorem reindexHom_successiveDescent (G : GroupoidScheme S) {X : Scheme.{u}}
    (u : X ⟶ (pullback G.source G.target).left) {F : G.objects.left.Modules}
    (α : (Scheme.Modules.pullback G.target.left).obj F ⟶
      (Scheme.Modules.pullback G.source.left).obj F)
    (e₁ : u ≫ G.comp.left ≫ G.target.left =
      (u ≫ (pullback.fst G.source G.target).left) ≫ G.target.left)
    (e₂ : (u ≫ (pullback.fst G.source G.target).left) ≫ G.source.left =
      (u ≫ (pullback.snd G.source G.target).left) ≫ G.target.left)
    (e₃ : (u ≫ (pullback.snd G.source G.target).left) ≫ G.source.left =
      u ≫ G.comp.left ≫ G.source.left) :
    reindexHom u (successiveDescent G α) =
      (Scheme.Modules.pullbackCongr e₁).hom.app F ≫
        reindexHom (u ≫ (pullback.fst G.source G.target).left) α ≫
        (Scheme.Modules.pullbackCongr e₂).hom.app F ≫
        reindexHom (u ≫ (pullback.snd G.source G.target).left) α ≫
        (Scheme.Modules.pullbackCongr e₃).hom.app F := by
  simp only [successiveDescent, reindexHom_comp, reindexHom_congr, reindexHom_assoc_rev,
    Category.assoc, pullbackCongr_hom_app_comp, pullbackCongr_hom_app_comp_assoc]

namespace QuasicoherentModule

/-- The section of the scheme of composable arrows pairing an arrow with its inverse, in the
order in which the composite is the identity at the target. -/
noncomputable def rightInverseSection (G : GroupoidScheme S) :
    G.arrows ⟶ pullback G.source G.target :=
  pullback.lift (𝟙 G.arrows) G.inverse (by simp [G.target_inverse])

/-- The section of the scheme of composable arrows pairing an arrow with its inverse, in the
order in which the composite is the identity at the source. -/
noncomputable def leftInverseSection (G : GroupoidScheme S) :
    G.arrows ⟶ pullback G.source G.target :=
  pullback.lift G.inverse (𝟙 G.arrows) (by simp [G.source_inverse])

/-- Composing an arrow with its inverse on the right gives the identity at the target. -/
theorem rightInverseSection_comp (G : GroupoidScheme S) :
    rightInverseSection G ≫ G.comp = G.target ≫ G.identity := by
  simpa [rightInverseSection] using
    G.right_inverse G.arrows (𝟙 G.arrows) (by simp [G.target_inverse])

/-- Composing an arrow with its inverse on the left gives the identity at the source. -/
theorem leftInverseSection_comp (G : GroupoidScheme S) :
    leftInverseSection G ≫ G.comp = G.source ≫ G.identity := by
  simpa [leftInverseSection] using
    G.left_inverse G.arrows (𝟙 G.arrows) (by simp [G.source_inverse])

/-- The reindexed cocycle law for the section pairing an arrow with its inverse on the right.
The four equalities are the comparisons of pullbacks that the pseudofunctoriality of pullback
forces into the statement; they are hypotheses so that any proof of them may be supplied. -/
theorem reindexed_cocycle_right (M : QuasicoherentModule G)
    (p₁ : (rightInverseSection G).left ≫ G.comp.left ≫ G.target.left = G.target.left)
    (p₂ : G.source.left = G.inverse.left ≫ G.target.left)
    (p₃ : G.inverse.left ≫ G.source.left =
      (rightInverseSection G).left ≫ G.comp.left ≫ G.source.left)
    (p₄ : (rightInverseSection G).left ≫ G.comp.left ≫ G.target.left =
      (rightInverseSection G).left ≫ G.comp.left ≫ G.source.left) :
    (Scheme.Modules.pullbackCongr p₁).hom.app M.module ≫ M.alpha ≫
        (Scheme.Modules.pullbackCongr p₂).hom.app M.module ≫
        reindexHom G.inverse.left M.alpha ≫
        (Scheme.Modules.pullbackCongr p₃).hom.app M.module =
      (Scheme.Modules.pullbackCongr p₄).hom.app M.module := by
  have hc := congrArg (reindexHom (rightInverseSection G).left) M.cocycle
  have hqfst : (rightInverseSection G).left ≫ (pullback.fst G.source G.target).left =
      𝟙 G.arrows.left :=
    congrArg Over.Hom.left (pullback.lift_fst (𝟙 G.arrows) G.inverse _)
  have hqsnd : (rightInverseSection G).left ≫ (pullback.snd G.source G.target).left =
      G.inverse.left :=
    congrArg Over.Hom.left (pullback.lift_snd (𝟙 G.arrows) G.inverse _)
  have hqcomp : (rightInverseSection G).left ≫ G.comp.left =
      G.target.left ≫ G.identity.left :=
    congrArg Over.Hom.left (rightInverseSection_comp G)
  have e₁ : (rightInverseSection G).left ≫ G.comp.left ≫ G.target.left =
      ((rightInverseSection G).left ≫ (pullback.fst G.source G.target).left) ≫
        G.target.left := by
    rwa [hqfst, Category.id_comp]
  have e₂ : ((rightInverseSection G).left ≫ (pullback.fst G.source G.target).left) ≫
      G.source.left =
      ((rightInverseSection G).left ≫ (pullback.snd G.source G.target).left) ≫
        G.target.left := by
    rwa [hqfst, hqsnd, Category.id_comp]
  have e₃ : ((rightInverseSection G).left ≫ (pullback.snd G.source G.target).left) ≫
      G.source.left = (rightInverseSection G).left ≫ G.comp.left ≫ G.source.left := by
    rwa [hqsnd]
  rw [reindexHom_successiveDescent G _ M.alpha e₁ e₂ e₃, reindexHom_assoc_rev] at hc
  rw [reindexHom_congr_source hqfst M.alpha, reindexHom_id_left,
    reindexHom_congr_source hqsnd M.alpha, reindexHom_congr_source hqcomp M.alpha,
    reindexHom_comp_identity G G.target.left M.alpha M.identity] at hc
  simpa only [Category.assoc, pullbackCongr_hom_app_comp,
    pullbackCongr_hom_app_comp_assoc] using hc

/-- The reindexed cocycle law for the section pairing an arrow with its inverse on the left. -/
theorem reindexed_cocycle_left (M : QuasicoherentModule G)
    (p₁ : (leftInverseSection G).left ≫ G.comp.left ≫ G.target.left =
      G.inverse.left ≫ G.target.left)
    (p₂ : G.inverse.left ≫ G.source.left = G.target.left)
    (p₃ : G.source.left = (leftInverseSection G).left ≫ G.comp.left ≫ G.source.left)
    (p₄ : (leftInverseSection G).left ≫ G.comp.left ≫ G.target.left =
      (leftInverseSection G).left ≫ G.comp.left ≫ G.source.left) :
    (Scheme.Modules.pullbackCongr p₁).hom.app M.module ≫
        reindexHom G.inverse.left M.alpha ≫
        (Scheme.Modules.pullbackCongr p₂).hom.app M.module ≫ M.alpha ≫
        (Scheme.Modules.pullbackCongr p₃).hom.app M.module =
      (Scheme.Modules.pullbackCongr p₄).hom.app M.module := by
  have hc := congrArg (reindexHom (leftInverseSection G).left) M.cocycle
  have hqfst : (leftInverseSection G).left ≫ (pullback.fst G.source G.target).left =
      G.inverse.left :=
    congrArg Over.Hom.left (pullback.lift_fst G.inverse (𝟙 G.arrows) _)
  have hqsnd : (leftInverseSection G).left ≫ (pullback.snd G.source G.target).left =
      𝟙 G.arrows.left :=
    congrArg Over.Hom.left (pullback.lift_snd G.inverse (𝟙 G.arrows) _)
  have hqcomp : (leftInverseSection G).left ≫ G.comp.left =
      G.source.left ≫ G.identity.left :=
    congrArg Over.Hom.left (leftInverseSection_comp G)
  have e₁ : (leftInverseSection G).left ≫ G.comp.left ≫ G.target.left =
      ((leftInverseSection G).left ≫ (pullback.fst G.source G.target).left) ≫
        G.target.left := by
    rwa [hqfst]
  have e₂ : ((leftInverseSection G).left ≫ (pullback.fst G.source G.target).left) ≫
      G.source.left =
      ((leftInverseSection G).left ≫ (pullback.snd G.source G.target).left) ≫
        G.target.left := by
    rwa [hqfst, hqsnd, Category.id_comp]
  have e₃ : ((leftInverseSection G).left ≫ (pullback.snd G.source G.target).left) ≫
      G.source.left = (leftInverseSection G).left ≫ G.comp.left ≫ G.source.left := by
    rwa [hqsnd, Category.id_comp]
  rw [reindexHom_successiveDescent G _ M.alpha e₁ e₂ e₃, reindexHom_assoc_rev] at hc
  rw [reindexHom_congr_source hqfst M.alpha, reindexHom_congr_source hqsnd M.alpha,
    reindexHom_id_left, reindexHom_congr_source hqcomp M.alpha,
    reindexHom_comp_identity G G.source.left M.alpha M.identity] at hc
  simpa only [Category.assoc, pullbackCongr_hom_app_comp,
    pullbackCongr_hom_app_comp_assoc] using hc

/-- The inverse of the descent morphism of a quasi-coherent module on a groupoid scheme: its
reindexing along the inverse map of the groupoid. -/
noncomputable def descentInverse (M : QuasicoherentModule G) :
    (Scheme.Modules.pullback G.source.left).obj M.module ⟶
      (Scheme.Modules.pullback G.target.left).obj M.module :=
  (Scheme.Modules.pullbackCongr
      (congrArg Over.Hom.left G.target_inverse).symm).hom.app M.module ≫
    reindexHom G.inverse.left M.alpha ≫
    (Scheme.Modules.pullbackCongr
      (congrArg Over.Hom.left G.source_inverse)).hom.app M.module

/-- A section of the composable arrows whose composite is `t ≫ identity` composes with the target
and with the source of the composite to `t`. -/
private theorem section_comp_target_source {X : Scheme.{u}} (G : GroupoidScheme S)
    (s : X ⟶ (pullback G.source G.target).left) (t : X ⟶ G.objects.left)
    (h : s ≫ G.comp.left = t ≫ G.identity.left) :
    s ≫ G.comp.left ≫ G.target.left = t ∧ s ≫ G.comp.left ≫ G.source.left = t := by
  rw [← Category.assoc, h, Category.assoc, identity_left_comp_target_left G, ← Category.assoc s,
    h, Category.assoc, identity_left_comp_source_left G]
  simp

/-- The descent morphism followed by its inverse is the identity. -/
theorem alpha_comp_descentInverse (M : QuasicoherentModule G) :
    M.alpha ≫ descentInverse M = 𝟙 _ := by
  obtain ⟨hp, hp2⟩ := section_comp_target_source G _ _
    (congrArg Over.Hom.left (rightInverseSection_comp G))
  have hc := reindexed_cocycle_right M hp (congrArg Over.Hom.left G.target_inverse).symm
    ((congrArg Over.Hom.left G.source_inverse).trans hp2.symm) (hp.trans hp2.symm)
  refine (cancel_epi ((Scheme.Modules.pullbackCongr hp).hom.app M.module)).1 ?_
  simpa [descentInverse, pullbackCongr_hom_app_comp, pullbackCongr_hom_app_comp_assoc] using
    congrArg (fun z ↦ z ≫ (Scheme.Modules.pullbackCongr hp2).hom.app M.module) hc

/-- The inverse of the descent morphism followed by the descent morphism is the identity. -/
theorem descentInverse_comp_alpha (M : QuasicoherentModule G) :
    descentInverse M ≫ M.alpha = 𝟙 _ := by
  obtain ⟨hp, hp2⟩ := section_comp_target_source G _ _
    (congrArg Over.Hom.left (leftInverseSection_comp G))
  have hc := reindexed_cocycle_left M
    (hp.trans (congrArg Over.Hom.left G.target_inverse).symm)
    (congrArg Over.Hom.left G.source_inverse) hp2.symm (hp.trans hp2.symm)
  refine (cancel_epi ((Scheme.Modules.pullbackCongr hp).hom.app M.module)).1 ?_
  simpa [descentInverse, pullbackCongr_hom_app_comp, pullbackCongr_hom_app_comp_assoc] using
    congrArg (fun z ↦ z ≫ (Scheme.Modules.pullbackCongr hp2).hom.app M.module) hc

/-- The descent morphism of a quasi-coherent module on a groupoid scheme is an isomorphism. -/
@[stacks 077Q]
instance alpha_isIso (M : QuasicoherentModule G) : IsIso M.alpha :=
  ⟨descentInverse M, alpha_comp_descentInverse M, descentInverse_comp_alpha M⟩

end QuasicoherentModule

end GroupoidScheme

end Stacks.Groupoids

end
