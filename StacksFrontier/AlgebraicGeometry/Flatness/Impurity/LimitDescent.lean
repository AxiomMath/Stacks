module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismAssociatedPoints.BaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.Pushforward
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Impurities
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPoints05KR
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningStratification.AffineFlatness

/-!
# Impurities descend along inverse limits

Let `P` be a pre-pure situation and let an impurity diagram for `P` have as its base an inverse
limit, in the category of schemes over `P.S`, of a cofiltered system of affine schemes over
`P.S`. Then the impurity is already visible at one stage of the system.

## Main definitions

* `AlgebraicGeometry.mapBase` transports an impurity diagram along a morphism of its bases over
  the original base.

## Main results

* `AlgebraicGeometry.exists_isImpurity_mapBase_of_isLimit`: an impurity on a cofiltered limit of
  affine schemes over the base descends to one of the schemes in the system.

## References

* [Stacks Project, Tag 05IZ](https://stacks.math.columbia.edu/tag/05IZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry

universe w v u

variable {J : Type v} [Category.{w} J] (D : J ⥤ Scheme.{u})

/-- A filtered colimit of commutative rings is the directed union of the images of its
structure maps. -/
private theorem jointly_surjective_of_isColimit
    {K : Type v} [Category.{w} K] [IsFiltered K]
    {F : K ⥤ CommRingCat.{u}} (c : Cocone F) (hc : IsColimit c) (x : c.pt) :
    ∃ j y, c.ι.app j y = x := by
  classical
  have : Nonempty K := IsFiltered.nonempty
  let r : K → Subring c.pt := fun j => (c.ι.app j).hom.range
  let R : Subring c.pt := ⨆ j, r j
  have hle {i j : K} (f : i ⟶ j) :
      (c.ι.app i).hom.range ≤ (c.ι.app j).hom.range := by
    rintro _ ⟨a, rfl⟩
    exact ⟨F.map f a, congrArg (fun g : F.obj i ⟶ c.pt => g a) (c.w f)⟩
  have hd : Directed (· ≤ ·) r := fun i j =>
    ⟨IsFiltered.max i j, hle (IsFiltered.leftToMax i j), hle (IsFiltered.rightToMax i j)⟩
  let c' : Cocone F :=
    { pt := CommRingCat.of R
      ι :=
        { app := fun j => CommRingCat.ofHom ((c.ι.app j).hom.codRestrict R
            (fun a => (le_iSup r j : r j ≤ R) ⟨a, rfl⟩))
          naturality := by
            intro i j f
            ext a
            exact Subtype.ext (congrArg (fun g : F.obj i ⟶ c.pt => g a) (c.w f)) } }
  let ι : c'.pt ⟶ c.pt := CommRingCat.ofHom R.subtype
  have he : hc.desc c' ≫ ι = 𝟙 c.pt := by
    apply hc.hom_ext
    intro j
    rw [← Category.assoc, hc.fac]
    rfl
  have hx : x ∈ R := by
    have h := congrArg (fun g : c.pt ⟶ c.pt => g x) he
    change ((hc.desc c' x : R) : c.pt) = x at h
    exact h ▸ (hc.desc c' x).property
  exact (Subring.mem_iSup_of_directed hd).mp hx

/-- Given a diagram `D` of schemes and an open `U` of `D.obj i`, this is the diagram of the
preimages of `U` in the schemes of the system that map to `D.obj i`. -/
@[simps] private noncomputable def affineOpensDiagram (i : J)
    (U : (D.obj i).Opens) : Over i ⥤ Scheme.{u} where
  obj j := D.map j.hom ⁻¹ᵁ U
  map {j k} f := (D.map f.left).resLE _ _
    (by rw [← Scheme.Hom.comp_preimage, ← D.map_comp, Over.w f])
  map_id j := by
    apply (cancel_mono (D.map j.hom ⁻¹ᵁ U).ι).mp
    simp
  map_comp {j k l} f g := by
    apply (cancel_mono (D.map l.hom ⁻¹ᵁ U).ι).mp
    simp [Category.assoc]

/-- The inclusion of the diagram of preimages of `U` into the original diagram. -/
@[simps] private noncomputable def affineOpensDiagramι (i : J) (U : (D.obj i).Opens) :
    affineOpensDiagram D i U ⟶ Over.forget i ⋙ D where
  app _ := Scheme.Opens.ι _
  naturality _ _ f := Scheme.Hom.resLE_comp_ι (D.map f.left) _

private instance (i : J) (U : (D.obj i).Opens) (j : Over i) :
    IsOpenImmersion ((affineOpensDiagramι D i U).app j) :=
  inferInstanceAs (IsOpenImmersion (D.map j.hom ⁻¹ᵁ U).ι)

/-- The preimage of `U` under the projection of a cone over `D` is a cone over the diagram of
preimages of `U`. -/
@[simps] private noncomputable def affineOpensCone (c : Cone D)
    (i : J) (U : (D.obj i).Opens) : Cone (affineOpensDiagram D i U) where
  pt := c.π.app i ⁻¹ᵁ U
  π :=
    { app j := (c.π.app j.left).resLE _ _ (by rw [← Scheme.Hom.comp_preimage, c.w])
      naturality j k f := by
        apply (cancel_mono (D.map k.hom ⁻¹ᵁ U).ι).mp
        simp only [affineOpensDiagram, Functor.const_obj_map,
          Scheme.Hom.resLE_comp_ι, Category.assoc]
        rw [← Category.assoc _ _ (D.map f.left), Scheme.Hom.resLE_comp_ι,
          Category.assoc, c.w f.left]
        simp }

attribute [local instance] CategoryTheory.isConnected_of_hasTerminal

variable (c : Cone D)

/-- Restricting a morphism to an open and its full preimage gives a cartesian square of open
immersions. -/
private theorem isPullback_resLE_ι {X Y : Scheme.{u}} (g : X ⟶ Y) (V : Y.Opens)
    (W : X.Opens) (e : W ≤ g ⁻¹ᵁ V) (he : g ⁻¹ᵁ V = W) :
    IsPullback (g.resLE V W e) W.ι V.ι g :=
  IsOpenImmersion.isPullback _ _ _ _ (Scheme.Hom.resLE_comp_ι g e).symm
    (by simp only [Scheme.Opens.opensRange_ι, he])

/-- The preimage of an open `U` of `D.obj i` under the projection of a limit cone over a
cofiltered diagram is the limit of the diagram of preimages of `U`. -/
private noncomputable def isLimitAffineOpensCone [IsCofiltered J] (hc : IsLimit c)
    (i : J) (U : (D.obj i).Opens) : IsLimit (affineOpensCone D c i U) :=
  isLimitOfIsPullbackOfIsConnected (affineOpensDiagramι D i U) (affineOpensCone D c i U)
    (c.whisker (Over.forget i))
    { hom := (c.π.app i ⁻¹ᵁ U).ι
      w j := (Scheme.Hom.resLE_comp_ι (c.π.app j.left) _).symm }
    (fun j => isPullback_resLE_ι (c.π.app j.left) (D.map j.hom ⁻¹ᵁ U) (c.π.app i ⁻¹ᵁ U) _
      (by rw [← Scheme.Hom.comp_preimage, c.w]))
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc)

/-- A section of `X` over `O` is the image of a section of `Y` over `W` under `g.appLE` as soon
as the global sections of the restricted schemes say so. -/
private theorem appLE_eq_of_resLE_appTop {X Y : Scheme.{u}} (g : X ⟶ Y) (W : Y.Opens)
    (O : X.Opens) (e : O ≤ g ⁻¹ᵁ W) (s : Γ(Y, W)) (r : Γ(X, O))
    (hs : (g.resLE W O e).appTop (W.topIso.inv s) = O.topIso.inv r) :
    r = g.appLE W O e s := by
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top] at hs
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply] at hs
  exact (O.topIso.commRingCatIsoToRingEquiv.symm.injective hs).symm

/-- The preimages of the affine opens of the schemes of a cofiltered system with affine
transition maps form a basis of the limit. -/
private theorem isBasis_preimage_affineOpen [IsCofiltered J] (hc : IsLimit c)
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f)] :
    TopologicalSpace.Opens.IsBasis
      { (c.π.app i ⁻¹ᵁ V : c.pt.Opens) | (i : J) (V : (D.obj i).Opens) (_ : IsAffineOpen V) } := by
  refine TopologicalSpace.Opens.isBasis_iff_nbhd.mpr fun {U x} hxU => ?_
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := J)
  obtain ⟨_, ⟨V, hV : IsAffineOpen V, rfl⟩, hxV, -⟩ :=
    (D.obj i).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (c.π.app i x)) isOpen_univ
  have (j : _) : IsAffine ((affineOpensDiagram D i V).op.obj j).unop := hV.preimage _
  have (j : _) : IsAffine ((affineOpensDiagram D i V).obj j) := hV.preimage _
  obtain ⟨r, hrU, hxr⟩ := IsAffineOpen.exists_basicOpen_le
    (Scheme.isAffine_of_isLimit _ (isLimitAffineOpensCone D c hc i V)) (V := U) ⟨x, hxU⟩ hxV
  obtain ⟨⟨j⟩, s, hs⟩ := jointly_surjective_of_isColimit _
    (isColimitOfPreserves Scheme.Γ (isLimitAffineOpensCone D c hc i V).op)
    ((c.π.app i ⁻¹ᵁ V).topIso.inv r)
  obtain ⟨s, rfl⟩ := (D.map j.hom ⁻¹ᵁ V).topIso.symm.commRingCatIsoToRingEquiv.surjective s
  have h : c.π.app j.left ⁻¹ᵁ D.map j.hom ⁻¹ᵁ V = c.π.app i ⁻¹ᵁ V := congr($(c.w j.hom) ⁻¹ᵁ V)
  have : r = (c.π.app j.left).appLE (D.map j.hom ⁻¹ᵁ V) (c.π.app i ⁻¹ᵁ V) h.ge s :=
    appLE_eq_of_resLE_appTop (c.π.app j.left) (D.map j.hom ⁻¹ᵁ V) (c.π.app i ⁻¹ᵁ V) h.ge s r hs
  refine ⟨_, ⟨j.left, _, (hV.preimage _).basicOpen s, rfl⟩, ?_⟩
  simp only [Functor.const_obj_obj, Scheme.preimage_basicOpen] at this ⊢
  rw [← c.pt.basicOpen_res_eq _ (eqToHom h.symm).op, ← CommRingCat.comp_apply,
    Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, ← this]
  exact ⟨hxr, hrU⟩

/-- A point of the limit specialises another as soon as it does so at every stage. -/
private theorem mem_closure_singleton_of_isLimit [IsCofiltered J] (hc : IsLimit c)
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f)]
    (x y : c.pt) (h : ∀ i, c.π.app i y ∈ closure {c.π.app i x}) :
    y ∈ closure {x} := by
  rw [mem_closure_iff]
  intro U hU hy
  obtain ⟨V, ⟨_, ⟨i, W, hW, rfl⟩, rfl⟩, hyV, hVU⟩ :=
    (isBasis_preimage_affineOpen D c hc).exists_subset_of_mem_open hy hU
  have hxW : c.π.app i x ∈ W := by simpa using (mem_closure_iff.mp (h i)) _ W.isOpen hyV
  exact ⟨x, hVU hxW, Set.mem_singleton x⟩

/-- In a cofiltered limit of schemes with affine transition maps, a quasi-compact set disjoint from
the closure of a point is disjoint from the preimage of the closure of its image at some stage. -/
private theorem exists_disjoint_closure_of_isLimit [IsCofiltered J] (hc : IsLimit c)
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (D.map f)]
    (x : c.pt) (K : Set c.pt) (hK : IsCompact K)
    (hx : Disjoint K (closure {x})) :
    ∃ i, Disjoint K ((c.π.app i) ⁻¹' closure {c.π.app i x}) := by
  have : Nonempty J := IsCofiltered.nonempty
  apply hK.elim_directed_family_closed
    (fun i => (c.π.app i) ⁻¹' closure {c.π.app i x})
    (fun i => isClosed_closure.preimage (c.π.app i).continuous)
  · exact Set.disjoint_left.mpr fun y hyK hy => Set.disjoint_left.mp hx hyK
      (mem_closure_singleton_of_isLimit D c hc x y (Set.mem_iInter.mp hy))
  · intro i j
    refine ⟨IsCofiltered.min i j, fun y hy => ?_, fun y hy => ?_⟩
    · simpa only [← Scheme.Hom.comp_apply, c.w, Set.image_singleton, Set.mem_preimage] using
        image_closure_subset_closure_image (D.map (IsCofiltered.minToLeft i j)).continuous
          ⟨c.π.app (IsCofiltered.min i j) y, hy, rfl⟩
    · simpa only [← Scheme.Hom.comp_apply, c.w, Set.image_singleton, Set.mem_preimage] using
        image_closure_subset_closure_image (D.map (IsCofiltered.minToRight i j)).continuous
          ⟨c.π.app (IsCofiltered.min i j) y, hy, rfl⟩

section Impurity

/-- Being locally of finite type is stable under base change along any fixed morphism. -/
private instance locallyOfFiniteType_isStableUnderBaseChangeAlong {X Y : Scheme.{u}} (g : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong (P := @LocallyOfFiniteType) g :=
  ⟨fun pb h => locallyOfFiniteType_isStableUnderBaseChange.of_isPullback pb h⟩

/-- Map an impurity diagram along a morphism of its base-change schemes over the original
base. The new base change is the chosen categorical pullback, and its point is the canonical
image of the old point. -/
public noncomputable def mapBase {P : AlgebraicGeometry.PrePureSituation.{u}}
    (D : AlgebraicGeometry.ImpurityDiagram P) {T' : Scheme.{u}} (g' : T' ⟶ P.S)
    (p : D.T ⟶ T') (hp : p ≫ g' = D.g) : AlgebraicGeometry.ImpurityDiagram P where
  T := T'
  g := g'
  t' := p.base D.t'
  t := p.base D.t
  specializes := p.base.hom.map_specializes D.specializes
  mapsToChosenPoint := by
    rw [← D.mapsToChosenPoint, ← Scheme.Hom.comp_apply]
    exact congrArg (fun f : D.T ⟶ P.S => f D.t) hp
  X_T := pullback P.f g'
  toX := pullback.fst P.f g'
  toT := pullback.snd P.f g'
  isPullback := IsPullback.of_hasPullback P.f g'
  xi := pullback.lift D.toX (D.toT ≫ p)
    (by rw [Category.assoc, hp, D.isPullback.w]) D.xi
  xi_liesOver := by
    rw [← D.xi_liesOver, ← Scheme.Hom.comp_apply]
    exact congrArg (fun f : D.X_T ⟶ T' => f D.xi)
      (pullback.lift_snd D.toX (D.toT ≫ p)
        (by rw [Category.assoc, hp, D.isPullback.w]))

/-- Base change of `f` along a diagram of schemes over its target. -/
private noncomputable abbrev impurityBaseChangeDiagram {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type v} [Category.{w} I] (F : I ⥤ Over S) : I ⥤ Scheme.{u} where
  obj i := pullback f (F.obj i).hom
  map {i j} a := pullback.map _ _ _ _ (𝟙 X) (F.map a).left (𝟙 S) (by simp) (by simp)
  map_id i := by simp
  map_comp a b := by simp [pullback.map_comp]

/-- The base change of an impurity diagram is a cone over the base-changed system. -/
private noncomputable abbrev impurityBaseChangeCone
    {P : PrePureSituation.{u}} (D : ImpurityDiagram P)
    {I : Type v} [Category.{w} I] (F : I ⥤ Over P.S) (c : Cone F)
    (e : Over.mk D.g ≅ c.pt) : Cone (impurityBaseChangeDiagram P.f F) where
  pt := D.X_T
  π :=
    { app i := pullback.lift D.toX (D.toT ≫ (e.hom ≫ c.π.app i).left)
        (by rw [Category.assoc, (e.hom ≫ c.π.app i).w]; exact D.isPullback.w)
      naturality i j a := by
        apply pullback.hom_ext
        · simp [impurityBaseChangeDiagram, pullback.map, Category.assoc, pullback.lift_fst]
        · simp only [impurityBaseChangeDiagram, pullback.map, Functor.const_obj_map,
            Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
          change 𝟙 _ ≫ (D.toT ≫ (e.hom ≫ c.π.app j).left) =
            D.toT ≫ (e.hom ≫ c.π.app i).left ≫ (F.map a).left
          rw [Category.id_comp, ← Over.comp_left, Category.assoc, c.w a] }

/-- Each leg of the base-changed cone is cartesian over the corresponding stage. -/
private theorem impurityBaseChangeCone_isPullback
    {P : PrePureSituation.{u}} (D : ImpurityDiagram P)
    {I : Type v} [Category.{w} I] (F : I ⥤ Over P.S) (c : Cone F)
    (e : Over.mk D.g ≅ c.pt) (i : I) :
    IsPullback ((impurityBaseChangeCone D F c e).π.app i) D.toT
      (pullback.snd P.f (F.obj i).hom) (e.hom ≫ c.π.app i).left := by
  apply IsPullback.of_right (h₁₂ := pullback.fst P.f (F.obj i).hom)
    (v₁₃ := P.f) (h₂₂ := (F.obj i).hom)
  · simpa [impurityBaseChangeCone, pullback.lift_fst, (e.hom ≫ c.π.app i).w] using D.isPullback
  · simp [impurityBaseChangeCone, pullback.lift_snd]
  · exact .of_hasPullback _ _

/-- The base change of an impurity diagram is the limit of the base-changed system. -/
private noncomputable def isLimitImpurityBaseChangeCone
    {P : PrePureSituation.{u}} (D : ImpurityDiagram P)
    {I : Type v} [Category.{w} I] [IsCofiltered I]
    (F : I ⥤ Over P.S) (c : Cone F) (hc : IsLimit c) (e : Over.mk D.g ≅ c.pt) :
    IsLimit (impurityBaseChangeCone D F c e) := by
  have : IsConnected I := IsCofiltered.isConnected _
  let cT : Cone (F ⋙ Over.forget P.S) :=
    { pt := D.T
      π :=
        { app i := (e.hom ≫ c.π.app i).left
          naturality i j a := by
            change 𝟙 _ ≫ _ = _ ≫ _
            simp only [Category.id_comp, Functor.comp_map, Over.forget_map,
              ← Over.comp_left, Category.assoc, c.w a] } }
  have hcT : IsLimit cT :=
    (isLimitOfPreserves (Over.forget P.S) hc).ofIsoLimit
      (Cone.ext ((Over.forget P.S).mapIso e.symm) (fun i => by simp [cT]))
  let α : impurityBaseChangeDiagram P.f F ⟶ F ⋙ Over.forget P.S :=
    { app i := pullback.snd _ _
      naturality i j a := by simp [impurityBaseChangeDiagram, pullback.lift_snd] }
  exact isLimitOfIsPullbackOfIsConnected α _ cT
    { hom := D.toT
      w i := by simp [α, cT, impurityBaseChangeCone, pullback.lift_snd] }
    (fun i => impurityBaseChangeCone_isPullback D F c e i) hcT

/-- A cartesian square of schemes is surjective onto compatible pairs of points. -/
@[sga "3 V 3.1"]
private theorem exists_preimage_of_isPullback
    {A X T S : Scheme.{u}} {a : A ⟶ X} {b : A ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (h : IsPullback a b f g) (x : X) (y : T) (hxy : f x = g y) :
    ∃ z, a z = x ∧ b z = y := by
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  refine ⟨h.isoPullback.inv z, ?_, ?_⟩
  · simpa only [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst] using hz₁
  · simpa only [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd] using hz₂

/-- An associated point of the pullback of a module along an isomorphism maps to an associated
point of the module. -/
private theorem mem_associatedPoints_image_iso
    {X Y : Scheme.{u}} (a : X ⟶ Y) [IsIso a] [IsLocallyNoetherian X]
    (F : Y.Modules) [F.IsQuasicoherent] (x : X)
    (hx : x ∈ Stacks.Divisors.associatedPoints ((Scheme.Modules.pullback a).obj F)) :
    a x ∈ Stacks.Divisors.associatedPoints F := by
  have : (Scheme.Modules.pushforward a).IsEquivalence :=
    Functor.IsEquivalence.mk' (Scheme.Modules.pushforward (inv a))
      (Scheme.Modules.pushforwardComp a (inv a) ≪≫
        Scheme.Modules.pushforwardCongr (IsIso.hom_inv_id a) ≪≫
        Scheme.Modules.pushforwardId X).symm
      (Scheme.Modules.pushforwardComp (inv a) a ≪≫
        Scheme.Modules.pushforwardCongr (IsIso.inv_hom_id a) ≪≫
        Scheme.Modules.pushforwardId Y)
  have hm : a x ∈ Stacks.Divisors.associatedPoints
      ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj F)) := by
    rw [← image_associatedPoints_eq_associatedPoints_pushforward a]
    exact ⟨x, hx, rfl⟩
  have he : Stacks.Divisors.associatedPoints F = Stacks.Divisors.associatedPoints
      ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj F)) :=
    Stacks.Divisors.associatedPoints_congr
      (asIso ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app F))
  rwa [he]

/-- The relative assassin is carried along an isomorphism of sources over the base. -/
private theorem mem_relativeAssassin_image_iso
    {X Y S : Scheme.{u}} (a : X ⟶ Y) [IsIso a]
    (f : Y ⟶ S) [LocallyOfFiniteType f] (G : Y.Modules) [G.IsQuasicoherent]
    (H : X.Modules) (eH : H ≅ (Scheme.Modules.pullback a).obj G)
    (b : X ⟶ S) (hb : a ≫ f = b) (x : X)
    (hx : x ∈ Stacks.Divisors.relativeAssassin b H) :
    a x ∈ Stacks.Divisors.relativeAssassin f G := by
  obtain ⟨s, z, hz, rfl⟩ := (Stacks.Divisors.mem_relativeAssassin b H x).mp hx
  have : LocallyOfFiniteType b := hb ▸ inferInstance
  let q : b.fiber s ⟶ f.fiber s :=
    pullback.map _ _ _ _ a (𝟙 _) (𝟙 S) (by simpa using hb.symm) (by simp)
  have hq : q ≫ f.fiberι s = b.fiberι s ≫ a := pullback.lift_fst _ _ _
  have : IsIso q := pullback.map_isIso _ _ _ _ a (𝟙 _) (𝟙 S) _ _
  have : IsLocallyNoetherian (b.fiber s) := isLocallyNoetherian_fiber_of_locallyOfFiniteType b s
  let eF : (Scheme.Modules.pullback (b.fiberι s)).obj H ≅
      (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback (f.fiberι s)).obj G) :=
    (Scheme.Modules.pullback (b.fiberι s)).mapIso eH ≪≫
      (Scheme.Modules.pullbackComp (b.fiberι s) a).app G ≪≫
      (Scheme.Modules.pullbackCongr hq.symm).app G ≪≫
      ((Scheme.Modules.pullbackComp q (f.fiberι s)).app G).symm
  exact (Stacks.Divisors.mem_relativeAssassin f G _).mpr
    ⟨s, q z, mem_associatedPoints_image_iso q ((Scheme.Modules.pullback (f.fiberι s)).obj G)
      z ((Stacks.Divisors.associatedPoints_congr eF) ▸ hz),
      congrArg (fun k : b.fiber s ⟶ Y => k z) hq⟩

/-- A point of the relative assassin of an arbitrary base change maps into the relative
assassin of the original morphism. -/
private theorem mem_relativeAssassin_of_isPullback
    {A X T S : Scheme.{u}} (a : A ⟶ X) (b : A ⟶ T)
    (f : X ⟶ S) (g : T ⟶ S) (h : IsPullback a b f g)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsQuasicoherent]
    (H : A.Modules) (eH : H ≅ (Scheme.Modules.pullback a).obj F)
    (x : A) (hx : x ∈ Stacks.Divisors.relativeAssassin b H) :
    a x ∈ Stacks.Divisors.relativeAssassin f F := by
  let e := h.isoPullback
  have he₁ : e.hom ≫ pullback.fst f g = a := h.isoPullback_hom_fst
  let eM : H ≅ (Scheme.Modules.pullback e.hom).obj
      ((Scheme.Modules.pullback (pullback.fst f g)).obj F) :=
    eH ≪≫ (Scheme.Modules.pullbackCongr he₁.symm).app F ≪≫
      ((Scheme.Modules.pullbackComp e.hom (pullback.fst f g)).app F).symm
  simpa only [← Scheme.Hom.comp_apply, he₁] using
    ((mem_relativeAssassin_pullback_iff f g F (e.hom x)).mp
      (mem_relativeAssassin_image_iso e.hom (pullback.snd f g) _ H eM b
        h.isoPullback_hom_snd x hx)).1

/-- An impurity on a cofiltered limit of affine schemes over the base is the pullback of an
impurity at some stage. -/
@[stacks 05IZ]
public theorem exists_isImpurity_mapBase_of_isLimit
    {P : AlgebraicGeometry.PrePureSituation.{u}}
    {I : Type v} [Category.{w} I] [IsCofiltered I]
    (F : I ⥤ Over P.S) (c : Cone F) (hc : IsLimit c)
    (D : AlgebraicGeometry.ImpurityDiagram P) (e : Over.mk D.g ≅ c.pt)
    (hF : ∀ i, IsAffine (F.obj i).left) (hD : AlgebraicGeometry.IsImpurity P D) :
    ∃ i, AlgebraicGeometry.IsImpurity P
      (mapBase D (F.obj i).hom (e.hom ≫ c.π.app i).left (e.hom ≫ c.π.app i).w) := by
  have (i : I) : IsAffine (F.obj i).left := hF i
  have : QuasiCompact D.toT :=
    MorphismProperty.of_isPullback D.isPullback (inferInstance : QuasiCompact P.f)
  have {i j : I} (a : i ⟶ j) : IsAffineHom ((impurityBaseChangeDiagram P.f F).map a) := by
    let m := (impurityBaseChangeDiagram P.f F).map a
    have hsq : IsPullback m (pullback.snd P.f (F.obj i).hom)
        (pullback.snd P.f (F.obj j).hom) (F.map a).left := by
      apply IsPullback.of_right (h₁₂ := pullback.fst P.f (F.obj j).hom)
        (v₁₃ := P.f) (h₂₂ := (F.obj j).hom)
      · simpa [m, impurityBaseChangeDiagram, pullback.lift_fst] using
          (IsPullback.of_hasPullback P.f (F.obj i).hom)
      · simp [m, impurityBaseChangeDiagram, pullback.lift_snd]
      · exact .of_hasPullback _ _
    exact MorphismProperty.of_isPullback hsq.flip
      (inferInstance : IsAffineHom (F.map a).left)
  obtain ⟨i, hi⟩ := exists_disjoint_closure_of_isLimit (impurityBaseChangeDiagram P.f F)
    (impurityBaseChangeCone D F c e) (isLimitImpurityBaseChangeCone D F c hc e) D.xi
    (D.toT ⁻¹' {D.t}) (D.toT.isCompact_preimage_singleton D.t) (by
      rw [← Scheme.Hom.range_fiberι, disjoint_comm, Set.disjoint_iff_inter_eq_empty]
      exact hD.2)
  let a := (impurityBaseChangeCone D F c e).π.app i
  have ha : a ≫ pullback.fst P.f (F.obj i).hom = D.toX := by
    simp [a, impurityBaseChangeCone, pullback.lift_fst]
  let G := (Scheme.Modules.pullback (pullback.fst P.f (F.obj i).hom)).obj P.F
  let eG : D.pulledBack P ≅ (Scheme.Modules.pullback a).obj G :=
    (Scheme.Modules.pullbackCongr ha.symm).app P.F ≪≫
      ((Scheme.Modules.pullbackComp a (pullback.fst P.f (F.obj i).hom)).app P.F).symm
  have hsq := impurityBaseChangeCone_isPullback D F c e i
  refine ⟨i, ?_, ?_⟩
  · exact mem_relativeAssassin_of_isPullback a D.toT (pullback.snd P.f (F.obj i).hom)
      (e.hom ≫ c.π.app i).left hsq G (D.pulledBack P) eG D.xi hD.1
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨hy, hyt⟩
    change y ∈ closure {a D.xi} at hy
    rw [Scheme.Hom.range_fiberι] at hyt
    obtain ⟨z, hz₁, hz₂⟩ := exists_preimage_of_isPullback hsq y D.t hyt
    exact Set.disjoint_left.mp hi hz₂ (show a z ∈ closure {a D.xi} by rwa [hz₁])

end Impurity

end AlgebraicGeometry
