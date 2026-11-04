module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.PresentedNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientOfCartesianRelation

/-!
# Inverse systems of algebraic spaces presented by systems of étale atlases

Let `V, R : I ⥤ C` be two systems of objects of the big fppf site of `S` with natural
transformations `s, t : R ⟶ V`, and suppose that at every index an algebraic space `X i` is given
together with a surjective étale atlas `V i ⟶ X i` whose kernel pair is `s, t`. Then the `X i`
form a system in a unique way compatible with the atlases, because a surjective étale atlas of an
algebraic space is the coequalizer of its kernel pair (Stacks 0262). When the source squares of
`R ⟶ V` are cartesian, so are the squares of atlases over the transition morphisms (Stacks 07VZ),
and the transition morphisms of the `X i` are affine as soon as those of the atlases are.

When the two systems of objects of the site have limits realised in the site, and an algebraic
space `X` has a surjective étale atlas by the limit of the atlases whose kernel pair is the limit
of the kernel pairs, then `X` is the limit of the system `X i`.

## Main definitions

* `AlgebraicGeometry.Space.AtlasFamily`: a family of algebraic spaces with surjective étale
  atlases presented by two systems of objects of the site.
* `AlgebraicGeometry.Space.AtlasFamily.diagram`: the induced system of algebraic spaces.
* `AlgebraicGeometry.Space.AtlasFamily.limitCone`: the cone over the system with vertex an
  algebraic space presented by the limits of the atlases and of their kernel pairs.

## Main results

* `AlgebraicGeometry.Space.isLimitOfIsLimitToScheme`: a cone in the big fppf site of `S`
  whose underlying cone of schemes is a limit is a limit.
* `AlgebraicGeometry.Space.AtlasFamily.isPullback_atlas`: the atlases are cartesian over the
  transition morphisms.
* `AlgebraicGeometry.Space.AtlasFamily.isAffineHom_diagram_map`: the transition morphisms are
  affine.
* `AlgebraicGeometry.Space.AtlasFamily.isLimitLimitCone`: an algebraic space presented by the
  limits of the atlases and of their kernel pairs is the limit of the system.

## References

* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 07VZ](https://stacks.math.columbia.edu/tag/07VZ)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A cone in the big fppf site of `S` over a connected diagram whose cone of schemes is a
limit is a limit.** -/
noncomputable def isLimitOfIsLimitToScheme {I : Type*} [Category* I] [IsConnected I]
    {D : I ⥤ BigFppfOver B S hS} {c : Cone D}
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) : IsLimit c :=
  isLimitOfReflects (BigFppfOver.forget B S hS)
    (isLimitOfReflects B.inclusion (IsLimit.ofIsoLimit hc (Functor.mapConeMapCone c).symm))

/-- The Yoneda image of a cone in the big fppf site whose cone of schemes is a limit is a limit
cone of presheaves. -/
noncomputable def isLimitYonedaMapCone {I : Type*} [Category* I] [IsConnected I]
    {D : I ⥤ BigFppfOver B S hS} {c : Cone D}
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) : IsLimit (yoneda.mapCone c) :=
  isLimitOfPreserves yoneda (isLimitOfIsLimitToScheme B S hS hc)

/-- A family of algebraic spaces over `S` with surjective étale atlases by a system `V` of
objects of the site, whose kernel pairs are presented by a system `R` with two natural
projections to `V`. -/
structure AtlasFamily (I : Type u) [Category.{u} I] where
  /-- The atlases. -/
  V : I ⥤ BigFppfOver B S hS
  /-- The kernel pairs. -/
  R : I ⥤ BigFppfOver B S hS
  /-- The first projection. -/
  s : R ⟶ V
  /-- The second projection. -/
  t : R ⟶ V
  /-- The algebraic spaces. -/
  X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- They are algebraic spaces. -/
  isAlgebraicSpace (i : I) : IsAlgebraicSpace B S hS (X i)
  /-- The atlas morphisms. -/
  v (i : I) : yoneda.obj (V.obj i) ⟶ X i
  /-- The atlas morphisms are surjective. -/
  surjective (i : I) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (v i)
  /-- The atlas morphisms are étale. -/
  etale (i : I) : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf (v i)
  /-- The kernel pairs. -/
  isPullback (i : I) : IsPullback (yoneda.map (s.app i)) (yoneda.map (t.app i)) (v i) (v i)

namespace AtlasFamily

variable {B S hS} {I : Type u} [Category.{u} I] (A : AtlasFamily B S hS I)

/-- Two morphisms to a stage atlas that are the two projections of a common morphism to the
kernel pair agree after composing with the atlas. -/
private theorem yoneda_map_comp_v_eq {i : I} {U W : BigFppfOver B S hS} (r : U ⟶ A.R.obj i)
    (x y : U ⟶ W) (w : W ⟶ A.V.obj i) (hx : x ≫ w = r ≫ A.s.app i) (hy : y ≫ w = r ≫ A.t.app i) :
    yoneda.map x ≫ (yoneda.map w ≫ A.v i) = yoneda.map y ≫ (yoneda.map w ≫ A.v i) := by
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp, hx, hy,
    Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, (A.isPullback i).w]

/-- The images of a transition morphism of the atlases identify the two projections. -/
theorem map_v_comp_eq {i j : I} (e : i ⟶ j) :
    yoneda.map (A.s.app i) ≫ (yoneda.map (A.V.map e) ≫ A.v j) =
      yoneda.map (A.t.app i) ≫ (yoneda.map (A.V.map e) ≫ A.v j) :=
  A.yoneda_map_comp_v_eq (A.R.map e) _ _ _ (A.s.naturality e).symm (A.t.naturality e).symm

/-- The transition morphism of the algebraic spaces, descended from that of the atlases. -/
noncomputable def map {i j : I} (e : i ⟶ j) : A.X i ⟶ A.X j :=
  (existsUnique_desc_of_surjective_etale_atlas B S hS (A.isAlgebraicSpace i).isSheaf (A.v i)
    (A.isPullback i) (A.surjective i) (A.etale i) (A.isAlgebraicSpace j).isSheaf
    (yoneda.map (A.V.map e) ≫ A.v j) (A.map_v_comp_eq e)).exists.choose

/-- The transition morphisms of the algebraic spaces commute with the atlases. -/
theorem v_map {i j : I} (e : i ⟶ j) : A.v i ≫ A.map e = yoneda.map (A.V.map e) ≫ A.v j :=
  (existsUnique_desc_of_surjective_etale_atlas B S hS (A.isAlgebraicSpace i).isSheaf (A.v i)
    (A.isPullback i) (A.surjective i) (A.etale i) (A.isAlgebraicSpace j).isSheaf
    (yoneda.map (A.V.map e) ≫ A.v j) (A.map_v_comp_eq e)).exists.choose_spec

/-- Two morphisms out of one of the algebraic spaces into a sheaf agree when they agree on its
atlas. -/
theorem hom_ext {i : I} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) {f g : A.X i ⟶ F}
    (h : A.v i ≫ f = A.v i ≫ g) : f = g :=
  hom_ext_of_etale_atlas B S hS (A.isAlgebraicSpace i).isSheaf hF (A.v i) (A.surjective i)
    (A.etale i) h

/-- The system of algebraic spaces. -/
noncomputable abbrev diagram : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u where
  obj := A.X
  map e := A.map e
  map_id i := A.hom_ext (A.isAlgebraicSpace i).isSheaf (by
    rw [A.v_map, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Category.comp_id])
  map_comp e e' := A.hom_ext (A.isAlgebraicSpace _).isSheaf (by
    rw [A.v_map, ← Category.assoc, A.v_map, Category.assoc, A.v_map, ← Category.assoc,
      ← Functor.map_comp, ← Functor.map_comp])

/-- The transition morphisms of the system of algebraic spaces. -/
theorem diagram_map {i j : I} (e : i ⟶ j) : A.diagram.map e = A.map e := rfl

/-- The atlas morphisms, as a natural transformation. -/
@[simps]
noncomputable def atlasMap : A.V ⋙ yoneda ⟶ A.diagram where
  app := A.v
  naturality _ _ e := (A.v_map e).symm

/-- **The atlases are cartesian over the transition morphisms** when the source squares of the
kernel pairs are cartesian (Stacks 07VZ). -/
theorem isPullback_atlas
    (hcart : ∀ {i j : I} (e : i ⟶ j), IsPullback (A.R.map e) (A.s.app i) (A.s.app j) (A.V.map e))
    {i j : I} (e : i ⟶ j) :
    IsPullback (yoneda.map (A.V.map e)) (A.v i) (A.v j) (A.diagram.map e) := by
  have houter : IsPullback (yoneda.map (A.t.app i) ≫ yoneda.map (A.V.map e))
      (yoneda.map (A.s.app i)) (A.v j) (A.v i ≫ A.diagram.map e) := by
    rw [diagram_map, A.v_map, ← Functor.map_comp, ← A.t.naturality, Functor.map_comp]
    exact ((hcart e).map yoneda).paste_horiz (A.isPullback j).flip
  exact isPullback_right_of_isPullback_of_surjective_etale B S hS
    (isAlgebraicSpace_yoneda B S hS (A.R.obj i)) (isAlgebraicSpace_yoneda B S hS (A.V.obj i))
    (isAlgebraicSpace_yoneda B S hS (A.V.obj i)) (A.isAlgebraicSpace i)
    (isAlgebraicSpace_yoneda B S hS (A.V.obj j)) (A.isAlgebraicSpace j) (A.v_map e).symm
    (A.isPullback i).flip houter (isSurjective_of_presheafSurjective B S hS _ (A.surjective i))
    ((isEtale_iff_presheaf_of_yoneda B S hS _).mpr (A.etale i))

/-- **The transition morphisms are affine** as soon as those of the atlases are and the source
squares of the kernel pairs are cartesian (Stacks 03WG). -/
theorem isAffineHom_diagram_map
    (hcart : ∀ {i j : I} (e : i ⟶ j), IsPullback (A.R.map e) (A.s.app i) (A.s.app j) (A.V.map e))
    {i j : I} (e : i ⟶ j)
    (he : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map (A.V.map e))) :
    IsAffineHom B S hS (A.diagram.map e) := by
  have hcartij := (A.isPullback_atlas hcart e).flip
  have hV : IsAffineHom B S hS (yoneda.map (A.V.map e)) :=
    isAffineHom_of_presheaf ((presheaf_yoneda_map_iff B S hS
      (P := @_root_.AlgebraicGeometry.IsAffineHom.{u}) inferInstance _).mpr he)
  have hsnd : IsAffineHom B S hS (pullback.snd (A.diagram.map e) (A.v j)) := by
    rw [← hcartij.isoPullback_inv_snd]
    exact isAffineHom_comp B S hS _ _ (isAffineHom_of_isIso hcartij.isoPullback.inv) hV
  refine ((isAffineHom_tfae_of_isAlgebraicSpace B S hS (A.diagram.map e) (A.isAlgebraicSpace i)
    (A.isAlgebraicSpace j)).out 4 2).1 ?_
  exact ⟨A.V.obj j, A.v j, isSurjective_of_presheafSurjective B S hS _ (A.surjective j),
      (isEtale_iff_presheaf_of_yoneda B S hS _).mpr (A.etale j), hsnd⟩

section Limit

variable (hcart : ∀ {i j : I} (e : i ⟶ j),
    IsPullback (A.R.map e) (A.s.app i) (A.s.app j) (A.V.map e))
  {cV : Cone A.V} (hcV : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cV))
  {cR : Cone A.R} (hcR : IsLimit ((BigFppfOver.toScheme B S hS).mapCone cR))
  (sL tL : cR.pt ⟶ cV.pt) (hsL : ∀ i, sL ≫ cV.π.app i = cR.π.app i ≫ A.s.app i)
  (htL : ∀ i, tL ≫ cV.π.app i = cR.π.app i ≫ A.t.app i)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
  (a : yoneda.obj cV.pt ⟶ X)
  (ha_surj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf a)
  (ha_et : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf a)
  (hker : IsPullback (yoneda.map sL) (yoneda.map tL) a a)

include hsL htL in
/-- The composite of the limit atlas with a stage atlas identifies the two projections of the
limit kernel pair. -/
theorem limit_comp_eq (i : I) :
    yoneda.map sL ≫ (yoneda.map (cV.π.app i) ≫ A.v i) =
      yoneda.map tL ≫ (yoneda.map (cV.π.app i) ≫ A.v i) :=
  A.yoneda_map_comp_v_eq (cR.π.app i) _ _ _ (hsL i) (htL i)

/-- The projection from `X` to a stage, descended along the limit atlas. -/
noncomputable def limitProj (i : I) : X ⟶ A.X i :=
  (existsUnique_desc_of_surjective_etale_atlas B S hS hX.isSheaf a hker ha_surj ha_et
    (A.isAlgebraicSpace i).isSheaf _ (A.limit_comp_eq sL tL hsL htL i)).exists.choose

/-- The projections from `X` to the stages commute with the atlases. -/
theorem a_limitProj (i : I) :
    a ≫ A.limitProj sL tL hsL htL hX a ha_surj ha_et hker i =
      yoneda.map (cV.π.app i) ≫ A.v i :=
  (existsUnique_desc_of_surjective_etale_atlas B S hS hX.isSheaf a hker ha_surj ha_et
    (A.isAlgebraicSpace i).isSheaf _ (A.limit_comp_eq sL tL hsL htL i)).exists.choose_spec

/-- The cone over the system with vertex `X`. -/
noncomputable abbrev limitCone : Cone A.diagram where
  pt := X
  π :=
    { app := A.limitProj sL tL hsL htL hX a ha_surj ha_et hker
      naturality i j e := by
        refine hom_ext_of_etale_atlas B S hS hX.isSheaf (A.isAlgebraicSpace j).isSheaf a
          ha_surj ha_et ?_
        change a ≫ 𝟙 X ≫ A.limitProj sL tL hsL htL hX a ha_surj ha_et hker j =
          a ≫ A.limitProj sL tL hsL htL hX a ha_surj ha_et hker i ≫ A.map e
        rw [Category.id_comp, A.a_limitProj, ← Category.assoc, A.a_limitProj, Category.assoc,
          A.v_map, ← Category.assoc, ← Functor.map_comp, cV.w] }

/-- The projections of `AlgebraicGeometry.Space.AtlasFamily.limitCone`. -/
theorem limitCone_π_app (i : I) :
    (A.limitCone sL tL hsL htL hX a ha_surj ha_et hker).π.app i =
      A.limitProj sL tL hsL htL hX a ha_surj ha_et hker i := rfl

include hcart hcV in
/-- **The base change of a stage atlas to the limit of the system is the limit of the atlases**,
for a cofiltered system with a terminal index and thin morphism types. -/
theorem isPullback_limit_atlas [IsCofiltered I] (hthin : ∀ i j : I, Subsingleton (i ⟶ j))
    (i₀ : I) (h₀ : ∀ i, Nonempty (i ⟶ i₀)) (c : Cone A.diagram) (hc : IsLimit c)
    (g : yoneda.obj cV.pt ⟶ c.pt) (hg : ∀ i, g ≫ c.π.app i = yoneda.map (cV.π.app i) ≫ A.v i) :
    IsPullback (yoneda.map (cV.π.app i₀)) g (A.v i₀) (c.π.app i₀) := by
  have : IsConnected I := IsCofiltered.isConnected I
  have hVlim := isLimitYonedaMapCone B S hS hcV
  have hP : ∀ i, IsPullback (yoneda.map (A.V.map (h₀ i).some)) (A.v i) (A.v i₀)
      (A.diagram.map (h₀ i).some) := fun i => A.isPullback_atlas hcart _
  have hid : A.V.map (h₀ i₀).some = 𝟙 _ := by
    rw [Subsingleton.elim (h₀ i₀).some (𝟙 i₀), CategoryTheory.Functor.map_id]
  have hcomm : ∀ {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : W ⟶ yoneda.obj (A.V.obj i₀))
      (y : W ⟶ c.pt) (hxy : x ≫ A.v i₀ = y ≫ c.π.app i₀) (i : I),
      x ≫ A.v i₀ = (y ≫ c.π.app i) ≫ A.diagram.map (h₀ i).some := fun x y hxy i => by
    rw [Category.assoc, c.w, hxy]
  let lift : ∀ {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : W ⟶ yoneda.obj (A.V.obj i₀))
      (y : W ⟶ c.pt) (hxy : x ≫ A.v i₀ = y ≫ c.π.app i₀), W ⟶ yoneda.obj cV.pt :=
    fun {W} x y hxy => hVlim.lift (Cone.mk W
      { app := fun i => (hP i).lift x (y ≫ c.π.app i) (hcomm x y hxy i)
        naturality := fun i j e => by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
            Functor.comp_map]
          refine (hP j).hom_ext ?_ ?_
          · rw [IsPullback.lift_fst, Category.assoc, ← Functor.map_comp,
              show A.V.map e ≫ A.V.map (h₀ j).some = A.V.map (h₀ i).some by
                rw [← Functor.map_comp, Subsingleton.elim (e ≫ (h₀ j).some) (h₀ i).some],
              IsPullback.lift_fst]
          · rw [IsPullback.lift_snd, Category.assoc, ← A.v_map, ← Category.assoc,
              IsPullback.lift_snd, Category.assoc, ← diagram_map, c.w] })
  have hlift : ∀ {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : W ⟶ yoneda.obj (A.V.obj i₀))
      (y : W ⟶ c.pt) (hxy : x ≫ A.v i₀ = y ≫ c.π.app i₀) (i : I),
      lift x y hxy ≫ yoneda.map (cV.π.app i) = (hP i).lift x (y ≫ c.π.app i) (hcomm x y hxy i) :=
    fun x y hxy i => hVlim.fac _ i
  refine IsPullback.of_isLimit' ⟨by rw [hg]⟩ (PullbackCone.IsLimit.mk _
    (fun s => lift s.fst s.snd s.condition) (fun s => ?_) (fun s => ?_) (fun s m hm₁ hm₂ => ?_))
  · rw [hlift _ _ s.condition]
    simpa [hid] using
      (hP i₀).lift_fst s.fst (s.snd ≫ c.π.app i₀) (hcomm s.fst s.snd s.condition i₀)
  · refine hc.hom_ext fun i => ?_
    rw [Category.assoc, hg, ← Category.assoc, hlift _ _ s.condition]
    exact IsPullback.lift_snd _ _ _ _
  · refine hVlim.hom_ext fun i => ?_
    show m ≫ yoneda.map (cV.π.app i) = lift s.fst s.snd s.condition ≫ yoneda.map (cV.π.app i)
    rw [hlift _ _ s.condition]
    refine (hP i).hom_ext ?_ ?_
    · rw [IsPullback.lift_fst, Category.assoc, ← Functor.map_comp, cV.w (h₀ i).some]
      exact hm₁
    · rw [IsPullback.lift_snd, Category.assoc, ← hg, ← Category.assoc, hm₂]

include hcV hcR hsL htL in
/-- **The limit kernel pair is the kernel pair of the limit atlas of the limit of the system.** -/
theorem isPullback_limit_kernel [IsCofiltered I] (c : Cone A.diagram) (hc : IsLimit c)
    (g : yoneda.obj cV.pt ⟶ c.pt) (hg : ∀ i, g ≫ c.π.app i = yoneda.map (cV.π.app i) ≫ A.v i) :
    IsPullback (yoneda.map sL) (yoneda.map tL) g g := by
  have : IsConnected I := IsCofiltered.isConnected I
  have hVlim := isLimitYonedaMapCone B S hS hcV
  have hRlim := isLimitYonedaMapCone B S hS hcR
  have hcomp : ∀ {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x y : T ⟶ yoneda.obj cV.pt)
      (hxy : x ≫ g = y ≫ g) (i : I),
      (x ≫ yoneda.map (cV.π.app i)) ≫ A.v i = (y ≫ yoneda.map (cV.π.app i)) ≫ A.v i := by
    intro T x y hxy i
    rw [Category.assoc, Category.assoc, ← hg, ← Category.assoc, hxy, Category.assoc]
  have hw : yoneda.map sL ≫ g = yoneda.map tL ≫ g := by
    refine hc.hom_ext fun i => ?_
    rw [Category.assoc, Category.assoc, hg]
    exact A.limit_comp_eq sL tL hsL htL i
  let lift : ∀ {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x y : T ⟶ yoneda.obj cV.pt)
      (hxy : x ≫ g = y ≫ g), T ⟶ yoneda.obj cR.pt :=
    fun {T} x y hxy => hRlim.lift (Cone.mk T
      { app := fun i => (A.isPullback i).lift (x ≫ yoneda.map (cV.π.app i))
          (y ≫ yoneda.map (cV.π.app i)) (hcomp x y hxy i)
        naturality := fun i j e => by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
            Functor.comp_map]
          refine (A.isPullback j).hom_ext ?_ ?_
          · rw [IsPullback.lift_fst, Category.assoc, ← Functor.map_comp, A.s.naturality,
              Functor.map_comp, ← Category.assoc, IsPullback.lift_fst, Category.assoc,
              ← Functor.map_comp, cV.w]
          · rw [IsPullback.lift_snd, Category.assoc, ← Functor.map_comp, A.t.naturality,
              Functor.map_comp, ← Category.assoc, IsPullback.lift_snd, Category.assoc,
              ← Functor.map_comp, cV.w] })
  have hlift : ∀ {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x y : T ⟶ yoneda.obj cV.pt)
      (hxy : x ≫ g = y ≫ g) (i : I), lift x y hxy ≫ yoneda.map (cR.π.app i) =
        (A.isPullback i).lift (x ≫ yoneda.map (cV.π.app i)) (y ≫ yoneda.map (cV.π.app i))
          (hcomp x y hxy i) :=
    fun x y hxy i => hRlim.fac _ i
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk _
    (fun s => lift s.fst s.snd s.condition) (fun s => ?_) (fun s => ?_) (fun s m hm₁ hm₂ => ?_))
  · refine hVlim.hom_ext fun i => ?_
    show (lift s.fst s.snd s.condition ≫ yoneda.map sL) ≫ yoneda.map (cV.π.app i) =
      s.fst ≫ yoneda.map (cV.π.app i)
    rw [Category.assoc, ← Functor.map_comp, hsL, Functor.map_comp, ← Category.assoc,
      hlift _ _ s.condition]
    exact IsPullback.lift_fst _ _ _ _
  · refine hVlim.hom_ext fun i => ?_
    show (lift s.fst s.snd s.condition ≫ yoneda.map tL) ≫ yoneda.map (cV.π.app i) =
      s.snd ≫ yoneda.map (cV.π.app i)
    rw [Category.assoc, ← Functor.map_comp, htL, Functor.map_comp, ← Category.assoc,
      hlift _ _ s.condition]
    exact IsPullback.lift_snd _ _ _ _
  · refine hRlim.hom_ext fun i => ?_
    show m ≫ yoneda.map (cR.π.app i) = lift s.fst s.snd s.condition ≫ yoneda.map (cR.π.app i)
    rw [hlift _ _ s.condition]
    refine (A.isPullback i).hom_ext ?_ ?_
    · rw [IsPullback.lift_fst, Category.assoc, ← Functor.map_comp, ← hsL, Functor.map_comp,
        ← Category.assoc, hm₁]
    · rw [IsPullback.lift_snd, Category.assoc, ← Functor.map_comp, ← htL, Functor.map_comp,
        ← Category.assoc, hm₂]

include hcart hcV hcR in
/-- The canonical comparison from `X` to the limit of the system is an isomorphism, for a
cofiltered system with a terminal index and thin morphism types. -/
theorem isIso_lift_limitCone [IsCofiltered I] (hthin : ∀ i j : I, Subsingleton (i ⟶ j))
    (i₀ : I) (h₀ : ∀ i, Nonempty (i ⟶ i₀)) :
    IsIso ((limit.isLimit A.diagram).lift (A.limitCone sL tL hsL htL hX a ha_surj ha_et hker)) := by
  let c := limit.cone A.diagram
  let hc := limit.isLimit A.diagram
  let φ := hc.lift (A.limitCone sL tL hsL htL hX a ha_surj ha_et hker)
  let g := a ≫ φ
  have hg : ∀ i, g ≫ c.π.app i = yoneda.map (cV.π.app i) ≫ A.v i := fun i => by
    show (a ≫ φ) ≫ c.π.app i = _
    rw [Category.assoc, hc.fac]
    exact A.a_limitProj sL tL hsL htL hX a ha_surj ha_et hker i
  have hLsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS) c.pt :=
    isSheaf_limit B S hS A.diagram fun i => (A.isAlgebraicSpace i).isSheaf
  have hpb := A.isPullback_limit_atlas hcart hcV hthin i₀ h₀ c hc g hg
  have hg_surj := presheaf_of_isPullback B S hS hpb (A.surjective i₀)
  have hg_et := presheaf_of_isPullback B S hS hpb (A.etale i₀)
  have hgker := A.isPullback_limit_kernel hcV hcR sL tL hsL htL c hc g hg
  obtain ⟨ψ, hψ, -⟩ := existsUnique_desc_of_surjective_etale_atlas B S hS hLsh g hgker hg_surj
    hg_et hX.isSheaf a hker.w
  refine ⟨ψ, hom_ext_of_etale_atlas B S hS hX.isSheaf hX.isSheaf a ha_surj ha_et ?_,
    hom_ext_of_etale_atlas B S hS hLsh hLsh g hg_surj hg_et ?_⟩
  all_goals rw [← Category.assoc, hψ, Category.comp_id]

include hcart hcV hcR in
/-- **An algebraic space presented by the limits of the atlases and of their kernel pairs is the
limit of the system**, for a cofiltered system with a terminal index and thin morphism types. -/
noncomputable def isLimitLimitCone [IsCofiltered I] (hthin : ∀ i j : I, Subsingleton (i ⟶ j))
    (i₀ : I) (h₀ : ∀ i, Nonempty (i ⟶ i₀)) :
    IsLimit (A.limitCone sL tL hsL htL hX a ha_surj ha_et hker) :=
  have := A.isIso_lift_limitCone hcart hcV hcR sL tL hsL htL hX a ha_surj ha_et hker hthin i₀ h₀
  IsLimit.ofIsoLimit (limit.isLimit A.diagram)
    (Cones.ext (asIso ((limit.isLimit A.diagram).lift
      (A.limitCone sL tL hsL htL hX a ha_surj ha_et hker))).symm (fun i => by simp))

end Limit

end AtlasFamily

end AlgebraicGeometry.Space

end
