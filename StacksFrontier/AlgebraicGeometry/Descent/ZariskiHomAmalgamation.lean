module

public import StacksFrontier.AlgebraicGeometry.Descent.ZariskiHomSheaf
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.Basic
public import StacksFrontier.Topology.Sheaves.Glueing.MapGluing

/-!
# Morphisms of sheaves of modules glue along an open covering

A family of morphisms of the restrictions of sheaves of modules `A` and `B` to the members of an
open covering of a scheme `X`, agreeing over the opens contained in two members, is the family of
restrictions of a single morphism `A ⟶ B`. Consequently the presheaf of morphisms
`CategoryTheory.Pseudofunctor.presheafHom` of the pullback pseudofunctor of sheaves of modules
satisfies the Zariski sheaf condition, and so does the pullback-sections presheaf of a
quasi-coherent module.

## Main definitions

* `AlgebraicGeometry.restrictHomOfPullbackHom`: a morphism of pullbacks along an open immersion
  read as a morphism of restrictions, by conjugation with
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.
* `AlgebraicGeometry.localApp`: the map on sections over an open `V` contained in `W` of a
  morphism of the restrictions to `W`.
* `AlgebraicGeometry.restrictLocal`: the restriction to a smaller open of a morphism of
  restrictions.
* `AlgebraicGeometry.typeSheaf`: the underlying sheaf of sets of a sheaf of modules.

## Main results

* `AlgebraicGeometry.exists_hom_of_localHoms`: morphisms of sheaves of modules glue along an open
  covering.
* `AlgebraicGeometry.bijective_toDescentData_map_opens`: descent of morphisms of sheaves of
  modules along a covering by open subschemes, in the form of
  `CategoryTheory.Pseudofunctor.IsPrestackFor`.
* `AlgebraicGeometry.isPrestackFor_zariski`: descent of morphisms for an arbitrary Zariski
  covering family.
* `AlgebraicGeometry.zariskiModuleHomAmalgamation`: the amalgamation property
  `AlgebraicGeometry.ZariskiModuleHomAmalgamation`.
* `AlgebraicGeometry.isPrestack_zariski`, `AlgebraicGeometry.isSheaf_presheafHom_zariski` and
  `AlgebraicGeometry.isSheafFor_presheafHom_zariski'`: the prestack property of the pullback
  pseudofunctor, the Zariski sheaf condition for the presheaf of morphisms, and the sheaf
  condition for a covering family.
* `AlgebraicGeometry.quasiCoherentPresheaf_isSheaf_zariski'`: the pullback-sections presheaf of a
  quasi-coherent module is a Zariski sheaf on the schemes over the base.
* `AlgebraicGeometry.restrictFunctorIsoPullback_comp`: the coherence of the comparison of
  restriction with pullback.
* `AlgebraicGeometry.restrictHomOfPullbackHom_pullHom`: under `restrictHomOfPullbackHom`, the
  pullback map of the presheaf of morphisms is the restriction of the restricted morphism.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` is defined as
`CategoryTheory.Adjunction.leftAdjointUniq` and so computes nothing. It,
`AlgebraicGeometry.Scheme.Modules.pullbackComp` and
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` are therefore handled through their mates
under `CategoryTheory.conjugateEquiv`, which are comparison morphisms of the pushforward with
identity components.

Sections of a restriction are sections of the module over the image
(`AlgebraicGeometry.Scheme.Modules.restrictAppIso` is the identity), but the two spellings are
not syntactically equal, and a rewrite whose motive mentions both is rejected at `implicit`
transparency. Composites are therefore written with `restrictAppIso` inserted explicitly, and
`AlgebraicGeometry.presheaf_map_eq`, `AlgebraicGeometry.presheaf_map_comp₂` and
`AlgebraicGeometry.conj_app_eq` identify any two composites of restriction maps around one
component of a morphism with the same source and target. Where a rewrite is still rejected, the
step is taken as a term, by `congrArg`.

## References

* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 04TQ](https://stacks.math.columbia.edu/tag/04TQ)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The mate of the canonical isomorphism between two left adjoints of one functor is the
identity. -/
lemma conjugateEquiv_leftAdjointUniq_hom {C D : Type*} [Category C] [Category D]
    {L L' : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (adj' : L' ⊣ R) :
    conjugateEquiv adj' adj (Adjunction.leftAdjointUniq adj adj').hom = 𝟙 R := by
  rw [← Equiv.eq_symm_apply]
  refine NatTrans.ext (funext fun X ↦ (adj.homEquiv X _).injective ?_)
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Adjunction.unit_leftAdjointUniq_hom_app]
  simp

/-- A composite of restriction maps of a module that returns to its starting open is the
identity, the homs of a poset being unique. -/
lemma presheaf_map_comp₄_self {X : Scheme.{u}} (M : X.Modules) {A B C D : (X.Opens)ᵒᵖ}
    (h₁ : A ⟶ B) (h₂ : B ⟶ C) (h₃ : C ⟶ D) (h₄ : D ⟶ A) :
    M.presheaf.map h₁ ≫ M.presheaf.map h₂ ≫ M.presheaf.map h₃ ≫ M.presheaf.map h₄ = 𝟙 _ := by
  have h : h₁ ≫ h₂ ≫ h₃ ≫ h₄ = 𝟙 A := Subsingleton.elim _ _
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, h]
  exact M.presheaf.map_id A

/-- The component of the restriction of a morphism of sheaves of modules along an open
immersion is its component at the image open. -/
lemma restrictFunctor_map_app {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (φ : M ⟶ N) (U : X.Opens) :
    ((Scheme.Modules.restrictFunctor f).map φ).app U = φ.app (f ''ᵁ U) := rfl

/-- The mate of `restrictFunctorComp` under `conjugateEquiv` is `pushforwardComp`. -/
lemma conjugateEquiv_restrictFunctorComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    conjugateEquiv ((Scheme.Modules.restrictAdjunction g).comp
        (Scheme.Modules.restrictAdjunction f))
      (Scheme.Modules.restrictAdjunction (f ≫ g))
      (Scheme.Modules.restrictFunctorComp f g).hom =
      (Scheme.Modules.pushforwardComp f g).hom := by
  refine NatTrans.ext (funext fun M ↦ Scheme.Modules.hom_ext _ _ fun U ↦ ?_)
  rw [conjugateEquiv_apply_app]
  simp only [Scheme.Modules.Hom.comp_app, Adjunction.comp_counit_app,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app,
    Scheme.Modules.restrictAdjunction_counit_app_app,
    Scheme.Modules.pushforwardComp_hom_app_app]
  simp only [restrictFunctor_map_app, Scheme.Modules.restrictAdjunction_counit_app_app,
    Functor.comp_obj, Scheme.Modules.pushforward_obj_presheaf_map]
  exact presheaf_map_comp₄_self M _ _ _ _

/-- The comparison of restriction with pullback is the mate of the identity. -/
lemma conjugateEquiv_restrictFunctorIsoPullback_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.restrictAdjunction f)
      (Scheme.Modules.restrictFunctorIsoPullback f).hom = 𝟙 (Scheme.Modules.pushforward f) :=
  conjugateEquiv_leftAdjointUniq_hom _ _

/-- **The coherence of the comparison of restriction with pullback.**  For a composite of
open immersions, the comparison of the restriction along the composite with the pullback along
it is the composite of the two comparisons, through `restrictFunctorComp` and `pullbackComp`. -/
lemma restrictFunctorIsoPullback_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    Scheme.Modules.restrictFunctorIsoPullback (f ≫ g) ≪≫
        (Scheme.Modules.pullbackComp f g).symm =
      Scheme.Modules.restrictFunctorComp f g ≪≫
        Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback g)
          (Scheme.Modules.restrictFunctor f) ≪≫
        Functor.isoWhiskerLeft (Scheme.Modules.pullback g)
          (Scheme.Modules.restrictFunctorIsoPullback f) := by
  refine Iso.ext ?_
  change (Scheme.Modules.restrictFunctorIsoPullback (f ≫ g)).hom ≫
        (Scheme.Modules.pullbackComp f g).inv =
      (Scheme.Modules.restrictFunctorComp f g).hom ≫
        Functor.whiskerRight (Scheme.Modules.restrictFunctorIsoPullback g).hom
          (Scheme.Modules.restrictFunctor f) ≫
        Functor.whiskerLeft (Scheme.Modules.pullback g)
          (Scheme.Modules.restrictFunctorIsoPullback f).hom
  refine (conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.restrictAdjunction (f ≫ g))).injective ?_
  rw [← conjugateEquiv_comp _ (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)) _,
    ← conjugateEquiv_comp _ ((Scheme.Modules.restrictAdjunction g).comp
      (Scheme.Modules.restrictAdjunction f)) _,
    ← conjugateEquiv_comp _ ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.restrictAdjunction f)) _,
    conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    conjugateEquiv_restrictFunctorComp, conjugateEquiv_restrictFunctorIsoPullback_hom,
    conjugateEquiv_restrictFunctorIsoPullback_hom,
    Scheme.Modules.conjugateEquiv_pullbackComp_inv,
    conjugateEquiv_restrictFunctorIsoPullback_hom]
  simp

/-- A morphism of pullbacks along an open immersion, read as a morphism of restrictions. -/
noncomputable def restrictHomOfPullbackHom {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {A B : Y.Modules}
    (θ : (Scheme.Modules.pullback f).obj A ⟶ (Scheme.Modules.pullback f).obj B) :
    Scheme.Modules.restrict A f ⟶ Scheme.Modules.restrict B f :=
  (Scheme.Modules.restrictFunctorIsoPullback f).hom.app A ≫ θ ≫
    (Scheme.Modules.restrictFunctorIsoPullback f).inv.app B

/-- `restrictHomOfPullbackHom` carries the pullback of a morphism to its restriction. -/
lemma restrictHomOfPullbackHom_map {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {A B : Y.Modules} (ψ : A ⟶ B) :
    restrictHomOfPullbackHom f ((Scheme.Modules.pullback f).map ψ) =
      (Scheme.Modules.restrictFunctor f).map ψ := by
  rw [restrictHomOfPullbackHom, ← Category.assoc,
    ← (Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality ψ]
  simp

/-- `restrictHomOfPullbackHom` is injective. -/
lemma restrictHomOfPullbackHom_injective {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {A B : Y.Modules} {θ₁ θ₂ : (Scheme.Modules.pullback f).obj A ⟶
      (Scheme.Modules.pullback f).obj B}
    (h : restrictHomOfPullbackHom f θ₁ = restrictHomOfPullbackHom f θ₂) : θ₁ = θ₂ := by
  rw [restrictHomOfPullbackHom, restrictHomOfPullbackHom] at h
  exact (Iso.cancel_iso_inv_right _ _ ((Scheme.Modules.restrictFunctorIsoPullback f).app B)).mp
    ((Iso.cancel_iso_hom_left ((Scheme.Modules.restrictFunctorIsoPullback f).app A) _ _).mp h)

/-- `restrictHomOfPullbackHom` carries the pullback map of the presheaf of morphisms along
`f ≫ g` to the restriction along `f` of the restricted morphism. -/
lemma restrictHomOfPullbackHom_pullHom_comp {Y Z X : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ X)
    [IsOpenImmersion f] [IsOpenImmersion g] {A B : X.Modules}
    (θ : (Scheme.Modules.pullback g).obj A ⟶ (Scheme.Modules.pullback g).obj B) :
    restrictHomOfPullbackHom (f ≫ g)
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := modulePullbackPseudofunctor)
          θ f (f ≫ g) (f ≫ g) rfl rfl) =
      (Scheme.Modules.restrictFunctorComp f g).hom.app A ≫
        (Scheme.Modules.restrictFunctor f).map (restrictHomOfPullbackHom g θ) ≫
        (Scheme.Modules.restrictFunctorComp f g).inv.app B := by
  have hcoh := restrictFunctorIsoPullback_comp f g
  have hA := congr_app (congrArg Iso.hom hcoh) A
  have hB := congr_app (congrArg Iso.inv hcoh) B
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc] at hA hB
  rw [modulePullbackPseudofunctor_pullHom f g (f ≫ g) rfl A B θ]
  simp only [restrictHomOfPullbackHom, Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp, Category.comp_id, Category.assoc]
  rw [reassoc_of% hA, hB]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app
      ((Scheme.Modules.pullback g).obj A)),
    ← (Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality θ]
  simp

/-- The comparison of restrictions along equal morphisms is the identity when the two
morphisms are literally the same. -/
lemma restrictFunctorCongr_rfl_hom_app {X Y : Scheme.{u}} {f : X ⟶ Y} [IsOpenImmersion f]
    (h : f = f) (M : Y.Modules) :
    (Scheme.Modules.restrictFunctorCongr h).hom.app M = 𝟙 _ := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  rw [Scheme.Modules.restrictFunctorCongr_hom_app_app]
  simp
  rfl

/-- The inverse comparison of restrictions along equal morphisms is the identity when the two
morphisms are literally the same. -/
lemma restrictFunctorCongr_rfl_inv_app {X Y : Scheme.{u}} {f : X ⟶ Y} [IsOpenImmersion f]
    (h : f = f) (M : Y.Modules) :
    (Scheme.Modules.restrictFunctorCongr h).inv.app M = 𝟙 _ := by
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  rw [Scheme.Modules.restrictFunctorCongr_inv_app_app]
  simp
  rfl

/-- `restrictHomOfPullbackHom` carries the pullback map of the presheaf of morphisms along a
factorisation `f ≫ g = h` to the restriction along `f` of the restricted morphism, up to
`restrictFunctorCongr`. -/
lemma restrictHomOfPullbackHom_pullHom {Y Z X : Scheme.{u}} (f : Y ⟶ Z) (g : Z ⟶ X) (h : Y ⟶ X)
    (w : f ≫ g = h) [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion h]
    {A B : X.Modules}
    (θ : (Scheme.Modules.pullback g).obj A ⟶ (Scheme.Modules.pullback g).obj B) :
    restrictHomOfPullbackHom h
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := modulePullbackPseudofunctor)
          θ f h h w w) =
      (Scheme.Modules.restrictFunctorCongr w).inv.app A ≫
        (Scheme.Modules.restrictFunctorComp f g).hom.app A ≫
        (Scheme.Modules.restrictFunctor f).map (restrictHomOfPullbackHom g θ) ≫
        (Scheme.Modules.restrictFunctorComp f g).inv.app B ≫
        (Scheme.Modules.restrictFunctorCongr w).hom.app B := by
  subst w
  rw [restrictFunctorCongr_rfl_inv_app, restrictFunctorCongr_rfl_hom_app, Category.id_comp,
    restrictHomOfPullbackHom_pullHom_comp f g θ]
  simp

section Gluing

variable {X : Scheme.{u}} {A B : X.Modules}

/-- Any two restriction maps of a module with the same source and target agree. -/
lemma presheaf_map_eq (M : X.Modules) {P Q : (X.Opens)ᵒᵖ} (h h' : P ⟶ Q) :
    M.presheaf.map h = M.presheaf.map h' := by
  rw [Subsingleton.elim h h']

/-- A composite of two restriction maps of a module is a restriction map, inside a longer
composite. -/
lemma presheaf_map_comp₂_assoc (M : X.Modules) {P Q R : (X.Opens)ᵒᵖ} (h₁ : P ⟶ Q) (h₂ : Q ⟶ R)
    (h₃ : P ⟶ R) {Z : Ab} (k : M.presheaf.obj R ⟶ Z) :
    M.presheaf.map h₁ ≫ M.presheaf.map h₂ ≫ k = M.presheaf.map h₃ ≫ k := by
  rw [← Category.assoc, ← Functor.map_comp, Subsingleton.elim (h₁ ≫ h₂) h₃]

/-- A composite of two restriction maps of a module is a restriction map. -/
lemma presheaf_map_comp₂ (M : X.Modules) {P Q R : (X.Opens)ᵒᵖ} (h₁ : P ⟶ Q) (h₂ : Q ⟶ R)
    (h₃ : P ⟶ R) : M.presheaf.map h₁ ≫ M.presheaf.map h₂ = M.presheaf.map h₃ := by
  rw [← Functor.map_comp, Subsingleton.elim (h₁ ≫ h₂) h₃]

/-- Naturality of a morphism of restrictions, read on the sections of the original modules. -/
lemma restrict_hom_naturality {W : X.Opens}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι)
    {U U' : W.toScheme.Opens} (j : U' ⟶ U) :
    A.presheaf.map (W.ι.opensFunctor.map j).op ≫ φ.app U' =
      φ.app U ≫ B.presheaf.map (W.ι.opensFunctor.map j).op :=
  φ.mapPresheaf.naturality j.op

/-- The sections map over `V ≤ W` of a morphism of restrictions to the open `W`. -/
noncomputable def localApp {W : X.Opens}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι)
    (V : X.Opens) (hV : V ≤ W) : Γ(A, V) ⟶ Γ(B, V) :=
  A.presheaf.map (homOfLE (Scheme.Hom.image_preimage_le W.ι V)).op ≫
    (A.restrictAppIso W.ι (W.ι ⁻¹ᵁ V)).inv ≫ φ.app (W.ι ⁻¹ᵁ V) ≫
      (B.restrictAppIso W.ι (W.ι ⁻¹ᵁ V)).hom ≫
      B.presheaf.map (homOfLE (le_of_eq
        (Stacks.AlgebraicGeometry.ModuleLimits.image_preimage_of_le hV).symm)).op

/-- The conjugate by `restrictAppIso` of a morphism of restrictions is natural. -/
lemma restrictAppIso_conj_naturality {W : X.Opens}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι)
    {U U' : W.toScheme.Opens} (j : U' ⟶ U) :
    (A.restrictAppIso W.ι U).inv ≫ φ.app U ≫ (B.restrictAppIso W.ι U).hom ≫
        B.presheaf.map (W.ι.opensFunctor.map j).op =
      A.presheaf.map (W.ι.opensFunctor.map j).op ≫ (A.restrictAppIso W.ι U').inv ≫
        φ.app U' ≫ (B.restrictAppIso W.ι U').hom := by
  have hnat : (A.restrict W.ι).presheaf.map j.op ≫ φ.app U' =
      φ.app U ≫ (B.restrict W.ι).presheaf.map j.op := φ.mapPresheaf.naturality j.op
  rw [presheaf_map_eq B _ (homOfLE (Scheme.Hom.image_mono W.ι (leOfHom j))).op,
    ← Scheme.Modules.map_restrictAppIso_hom W.ι B j.op, ← reassoc_of% hnat,
    Scheme.Modules.restrictAppIso_inv_map_assoc W.ι A j.op,
    presheaf_map_eq A (homOfLE (Scheme.Hom.image_mono W.ι (leOfHom j))).op
      (W.ι.opensFunctor.map j).op]

/-- The shape of the naturality of `localApp`, with the comparison maps as variables. -/
lemma localApp_naturality_aux {W : X.Opens}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι)
    {U U' : W.toScheme.Opens} (j : U' ⟶ U) {V V' : X.Opens}
    (a : op V ⟶ op (W.ι ''ᵁ U)) (b : op (W.ι ''ᵁ U) ⟶ op V) (c : op V ⟶ op V')
    (a' : op V' ⟶ op (W.ι ''ᵁ U')) (b' : op (W.ι ''ᵁ U') ⟶ op V') :
    (A.presheaf.map a ≫ (A.restrictAppIso W.ι U).inv ≫ φ.app U ≫
        (B.restrictAppIso W.ι U).hom ≫ B.presheaf.map b) ≫ B.presheaf.map c =
      A.presheaf.map c ≫ A.presheaf.map a' ≫ (A.restrictAppIso W.ι U').inv ≫ φ.app U' ≫
        (B.restrictAppIso W.ι U').hom ≫ B.presheaf.map b' := by
  have hb : B.presheaf.map b ≫ B.presheaf.map c =
      B.presheaf.map (W.ι.opensFunctor.map j).op ≫ B.presheaf.map b' := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact presheaf_map_eq B _ _
  have ha : A.presheaf.map a ≫ A.presheaf.map (W.ι.opensFunctor.map j).op =
      A.presheaf.map c ≫ A.presheaf.map a' := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact presheaf_map_eq A _ _
  rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, hb,
    reassoc_of% (restrictAppIso_conj_naturality φ j), ← Category.assoc (A.presheaf.map a), ha,
    Category.assoc]

/-- **`localApp` is natural**: it commutes with the restriction maps of `A` and `B`. -/
lemma localApp_naturality {W : X.Opens}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι)
    {V V' : X.Opens} (hV : V ≤ W) (hV' : V' ≤ W) (i : V' ⟶ V) :
    localApp φ V hV ≫ B.presheaf.map i.op = A.presheaf.map i.op ≫ localApp φ V' hV' := by
  rw [localApp, localApp]
  exact localApp_naturality_aux φ ((TopologicalSpace.Opens.map W.ι.base).map i) _ _ _ _ _

/-- On an open of the form `W.ι ''ᵁ U`, `localApp` is the component of `φ` at `U`. -/
lemma localApp_image {W : X.Opens}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι)
    (U : W.toScheme.Opens) :
    localApp φ (W.ι ''ᵁ U) (Scheme.Opens.ι_image_le W U) =
      (A.restrictAppIso W.ι U).inv ≫ φ.app U ≫ (B.restrictAppIso W.ι U).hom := by
  have hj : U ≤ W.ι ⁻¹ᵁ (W.ι ''ᵁ U) := le_of_eq (W.ι.preimage_image_eq U).symm
  rw [localApp, presheaf_map_eq B _ (W.ι.opensFunctor.map (homOfLE hj)).op,
    restrictAppIso_conj_naturality φ (homOfLE hj),
    ← Category.assoc (A.presheaf.map _), presheaf_map_comp₂ A _ _ (𝟙 _),
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The underlying sheaf of types of a sheaf of modules on a scheme. -/
noncomputable def typeSheaf (A : X.Modules) : TopCat.Sheaf (Type u) X :=
  ⟨A.presheaf ⋙ forget Ab,
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget Ab) A.presheaf).mp A.isSheaf⟩

/-- A round trip of restriction maps of the structure sheaf is the identity. -/
lemma structurePresheaf_comp_self {P Q : (X.Opens)ᵒᵖ} (h₁ : P ⟶ Q) (h₂ : Q ⟶ P)
    (r : ToType (X.presheaf.obj P)) :
    X.presheaf.map h₂ (X.presheaf.map h₁ r) = r := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp, Subsingleton.elim (h₁ ≫ h₂) (𝟙 _),
    CategoryTheory.Functor.map_id]
  rfl

/-- `localApp` is linear over the structure sheaf. -/
lemma localApp_smul {W : X.Opens}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι)
    (V : X.Opens) (hV : V ≤ W) (r : Γ(X, V)) (s : Γ(A, V)) :
    localApp φ V hV (r • s) = r • localApp φ V hV s := by
  rw [localApp]
  simp only [CategoryTheory.comp_apply, Scheme.Modules.map_smul,
    Scheme.Modules.smul_restrictAppIso_inv_apply, Scheme.Modules.Hom.app_smul,
    Scheme.Modules.smul_restrictAppIso_hom_apply, CategoryTheory.Iso.hom_inv_id_apply]
  rw [structurePresheaf_comp_self]

/-- The local morphism of sheaves of types attached to a morphism of restrictions. -/
noncomputable def localSheafHom {W : X.Opens}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι) :
    TopCat.Sheaf.LocalSheafHom (typeSheaf A) (typeSheaf B) W where
  app V hV := fun s ↦ localApp φ V hV s
  naturality _ _ hV hV' i s := ConcreteCategory.congr_hom (localApp_naturality φ hV hV' i) s

/-- Two composites of restriction maps around a morphism of restrictions, with matching
endpoints, agree. -/
lemma conj_app_eq {W : X.Opens}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι)
    {U U' : W.toScheme.Opens} (j : U' ⟶ U) {V V' : X.Opens}
    (a : op V ⟶ op (W.ι ''ᵁ U)) (b : op (W.ι ''ᵁ U) ⟶ op V')
    (a' : op V ⟶ op (W.ι ''ᵁ U')) (b' : op (W.ι ''ᵁ U') ⟶ op V') :
    A.presheaf.map a ≫ (A.restrictAppIso W.ι U).inv ≫ φ.app U ≫
        (B.restrictAppIso W.ι U).hom ≫ B.presheaf.map b =
      A.presheaf.map a' ≫ (A.restrictAppIso W.ι U').inv ≫ φ.app U' ≫
        (B.restrictAppIso W.ι U').hom ≫ B.presheaf.map b' := by
  rw [← presheaf_map_comp₂ B (W.ι.opensFunctor.map j).op b' b,
    reassoc_of% (restrictAppIso_conj_naturality φ j), ← Category.assoc (A.presheaf.map a),
    presheaf_map_comp₂ A a (W.ι.opensFunctor.map j).op a']

/-- `conj_app_eq` with the composites on the left and the right split in two. -/
lemma conj_app_eq₂ {W : X.Opens}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι)
    {U U' : W.toScheme.Opens} (j : U' ⟶ U) {V V' P Q : X.Opens}
    (a₁ : op V ⟶ op P) (a₂ : op P ⟶ op (W.ι ''ᵁ U)) (b₁ : op (W.ι ''ᵁ U) ⟶ op Q)
    (b₂ : op Q ⟶ op V') (a' : op V ⟶ op (W.ι ''ᵁ U')) (b' : op (W.ι ''ᵁ U') ⟶ op V') :
    A.presheaf.map a₁ ≫ A.presheaf.map a₂ ≫ (A.restrictAppIso W.ι U).inv ≫ φ.app U ≫
        (B.restrictAppIso W.ι U).hom ≫ B.presheaf.map b₁ ≫ B.presheaf.map b₂ =
      A.presheaf.map a' ≫ (A.restrictAppIso W.ι U').inv ≫ φ.app U' ≫
        (B.restrictAppIso W.ι U').hom ≫ B.presheaf.map b' := by
  rw [presheaf_map_comp₂_assoc A a₁ a₂ (a₁ ≫ a₂), presheaf_map_comp₂ B b₁ b₂ (b₁ ≫ b₂)]
  exact conj_app_eq φ j _ _ a' b'

/-- `conj_app_eq₂` with the identity comparison isomorphisms of a second open in the way. -/
lemma conj_app_eq₃ {W W₀ : X.Opens}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι)
    {U U' : W.toScheme.Opens} (j : U' ⟶ U) {U₀ : W₀.toScheme.Opens} {V V' : X.Opens}
    (a₁ : op V ⟶ op (W₀.ι ''ᵁ U₀)) (a₂ : op (W₀.ι ''ᵁ U₀) ⟶ op (W.ι ''ᵁ U))
    (b₁ : op (W.ι ''ᵁ U) ⟶ op (W₀.ι ''ᵁ U₀)) (b₂ : op (W₀.ι ''ᵁ U₀) ⟶ op V')
    (a' : op V ⟶ op (W.ι ''ᵁ U')) (b' : op (W.ι ''ᵁ U') ⟶ op V') :
    A.presheaf.map a₁ ≫ (A.restrictAppIso W₀.ι U₀).inv ≫
        (A.presheaf.map a₂ ≫ (A.restrictAppIso W.ι U).inv ≫ φ.app U ≫
          (B.restrictAppIso W.ι U).hom ≫ B.presheaf.map b₁) ≫
        (B.restrictAppIso W₀.ι U₀).hom ≫ B.presheaf.map b₂ =
      A.presheaf.map a' ≫ (A.restrictAppIso W.ι U').inv ≫ φ.app U' ≫
        (B.restrictAppIso W.ι U').hom ≫ B.presheaf.map b' :=
  conj_app_eq₂ φ j a₁ a₂ b₁ b₂ a' b'

/-- The restriction to a smaller open of a morphism of restrictions. -/
noncomputable def restrictLocal {V W : X.Opens}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι) (hV : V ≤ W) :
    Scheme.Modules.restrict A V.ι ⟶ Scheme.Modules.restrict B V.ι :=
  (Scheme.Modules.restrictFunctorCongr (Scheme.homOfLE_ι X hV)).inv.app A ≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE hV) W.ι).hom.app A ≫
    (Scheme.Modules.restrictFunctor (X.homOfLE hV)).map φ ≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE hV) W.ι).inv.app B ≫
    (Scheme.Modules.restrictFunctorCongr (Scheme.homOfLE_ι X hV)).hom.app B

/-- The component of `restrictLocal φ hV` at `U`, written through arbitrary restriction maps
`a` and `b`. -/
lemma restrictLocal_app {V W : X.Opens}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι) (hV : V ≤ W)
    (U : V.toScheme.Opens)
    (a : op (V.ι ''ᵁ U) ⟶ op (W.ι ''ᵁ (X.homOfLE hV ''ᵁ U)))
    (b : op (W.ι ''ᵁ (X.homOfLE hV ''ᵁ U)) ⟶ op (V.ι ''ᵁ U)) :
    (restrictLocal φ hV).app U =
      A.presheaf.map a ≫ (A.restrictAppIso W.ι (X.homOfLE hV ''ᵁ U)).inv ≫
        φ.app (X.homOfLE hV ''ᵁ U) ≫
        (B.restrictAppIso W.ι (X.homOfLE hV ''ᵁ U)).hom ≫ B.presheaf.map b := by
  rw [restrictLocal]
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.restrictFunctorCongr_inv_app_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app, restrictFunctor_map_app]
  refine ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) (presheaf_map_comp₂ A _ _ a))).trans ?_
  exact congrArg (A.presheaf.map a ≫ ·) (congrArg (φ.app (X.homOfLE hV ''ᵁ U) ≫ ·)
    (presheaf_map_comp₂ B _ _ b))

/-- The section map of a morphism of restrictions is the section map of its restriction. -/
lemma localApp_restrictLocal {V W : X.Opens}
    (φ : Scheme.Modules.restrict A W.ι ⟶ Scheme.Modules.restrict B W.ι) (hV : V ≤ W) :
    localApp φ V hV = localApp (restrictLocal φ hV) V le_rfl := by
  have himg : W.ι ''ᵁ (X.homOfLE hV ''ᵁ (V.ι ⁻¹ᵁ V)) = V.ι ''ᵁ (V.ι ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_image]
    simp only [Scheme.homOfLE_ι]
  rw [localApp, localApp, restrictLocal_app φ hV (V.ι ⁻¹ᵁ V) (eqToHom himg).op
    (eqToHom himg.symm).op]
  have hU : W.ι ⁻¹ᵁ V = X.homOfLE hV ''ᵁ (V.ι ⁻¹ᵁ V) := by
    rw [Scheme.Opens.ι_preimage_self, ← Scheme.opensRange_homOfLE hV]
    simp
  exact (conj_app_eq₃ φ (homOfLE (le_of_eq hU)) _ _ _ _ _ _).symm

/-- A section of a module on `V` is determined by its restrictions to the `V ⊓ W i`. -/
lemma section_eq_of_cover {ι : Type*} {W : ι → X.Opens} (hW : ⨆ i, W i = ⊤) {V : X.Opens}
    (s t : ToType Γ(B, V))
    (h : ∀ i, B.presheaf.map (homOfLE (inf_le_left : V ⊓ W i ≤ V)).op s =
      B.presheaf.map (homOfLE (inf_le_left : V ⊓ W i ≤ V)).op t) : s = t := by
  refine B.isSheaf.section_ext (U := op V) ?_
  intro x hx
  have hx' : x ∈ (⨆ i, W i : X.Opens) := hW ▸ trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
  exact ⟨V ⊓ W i, inf_le_left, ⟨hx, hi⟩, h i⟩

/-- **Morphisms of sheaves of modules glue along an open covering.**  A family of morphisms of
the restrictions of `A` and `B` to the members of an open covering of `X`, agreeing on the opens
contained in two members, is the family of restrictions of a morphism `A ⟶ B`. -/
theorem exists_hom_of_localHoms {ι : Type*} {W : ι → X.Opens} (hW : ⨆ i, W i = ⊤)
    (φ : ∀ i, Scheme.Modules.restrict A (W i).ι ⟶ Scheme.Modules.restrict B (W i).ι)
    (hφ : ∀ i j (V : X.Opens) (hVi : V ≤ W i) (hVj : V ≤ W j),
      localApp (φ i) V hVi = localApp (φ j) V hVj) :
    ∃ ψ : A ⟶ B, ∀ i, (Scheme.Modules.restrictFunctor (W i).ι).map ψ = φ i := by
  obtain ⟨ψ₀, hψ₀, -⟩ := TopCat.Sheaf.existsUnique_hom_of_localHom W hW (typeSheaf A)
    (typeSheaf B) (fun i ↦ localSheafHom (φ i))
    (fun i j V hVi hVj ↦ funext fun s ↦ ConcreteCategory.congr_hom (hφ i j V hVi hVj) s)
  obtain ⟨g, hg⟩ : ∃ g : ∀ V : (X.Opens)ᵒᵖ, ToType Γ(A, V.unop) → ToType Γ(B, V.unop),
      ∀ V, g V = ψ₀.1.app V := ⟨fun V ↦ ψ₀.1.app V, fun _ ↦ rfl⟩
  have hgnat : ∀ {V V' : (X.Opens)ᵒᵖ} (f : V ⟶ V') (s : ToType Γ(A, V.unop)),
      g V' (A.presheaf.map f s) = B.presheaf.map f (g V s) := by
    intro V V' f s
    rw [hg, hg]
    exact NatTrans.naturality_apply ψ₀.1 f s
  have key : ∀ (i : ι) (V : (X.Opens)ᵒᵖ) (s : ToType Γ(A, V.unop)),
      B.presheaf.map (homOfLE (inf_le_left : V.unop ⊓ W i ≤ V.unop)).op (g V s) =
        localApp (φ i) (V.unop ⊓ W i) inf_le_right
          (A.presheaf.map (homOfLE (inf_le_left : V.unop ⊓ W i ≤ V.unop)).op s) := by
    intro i V s
    rw [← hgnat (homOfLE (inf_le_left : V.unop ⊓ W i ≤ V.unop)).op s, hg]
    exact congrFun (hψ₀ i (V.unop ⊓ W i) inf_le_right) _
  have hadd : ∀ (V : (X.Opens)ᵒᵖ) (s t : ToType Γ(A, V.unop)),
      g V (s + t) = g V s + g V t := by
    intro V s t
    refine section_eq_of_cover hW _ _ fun i ↦ ?_
    simp only [map_add, key i V]
  have hsmul : ∀ (V : (X.Opens)ᵒᵖ) (r : ToType Γ(X, V.unop)) (s : ToType Γ(A, V.unop)),
      g V (r • s) = r • g V s := by
    intro V r s
    refine section_eq_of_cover hW _ _ fun i ↦ ?_
    simp only [Scheme.Modules.map_smul, key i V, localApp_smul]
  let ψ : A ⟶ B := ⟨PresheafOfModules.homMk
    { app := fun V ↦ AddCommGrpCat.ofHom (AddMonoidHom.mk' (g V) (hadd V))
      naturality := fun V V' f ↦ by
        ext s
        exact hgnat f s } hsmul⟩
  refine ⟨ψ, fun i ↦ ?_⟩
  refine Scheme.Modules.hom_ext _ _ fun U ↦ ?_
  refine (restrictFunctor_map_app (W i).ι _ U).trans ?_
  have hψ : ∀ (V : X.Opens) (hV : V ≤ W i), ψ.app V = localApp (φ i) V hV := by
    intro V hV
    ext s
    have h := congrFun (hψ₀ i V hV) s
    rw [← hg (op V)] at h
    exact h
  rw [hψ _ (Scheme.Opens.ι_image_le (W i) U), localApp_image]
  simp only [Scheme.Modules.restrictAppIso, Iso.refl_inv, Iso.refl_hom]
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The restriction of `restrictHomOfPullbackHom W.ι θ` to `V ≤ W` is
`restrictHomOfPullbackHom V.ι` of the pullback of `θ`. -/
lemma restrictLocal_restrictHomOfPullbackHom {V W : X.Opens} (hV : V ≤ W)
    (θ : (Scheme.Modules.pullback W.ι).obj A ⟶ (Scheme.Modules.pullback W.ι).obj B) :
    restrictLocal (restrictHomOfPullbackHom W.ι θ) hV =
      restrictHomOfPullbackHom V.ι
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := modulePullbackPseudofunctor)
          θ (X.homOfLE hV) V.ι V.ι (Scheme.homOfLE_ι X hV) (Scheme.homOfLE_ι X hV)) :=
  (restrictHomOfPullbackHom_pullHom _ _ _ (Scheme.homOfLE_ι X hV) θ).symm

/-- **Descent of morphisms of sheaves of modules along a covering by open subschemes.** -/
theorem bijective_toDescentData_map_opens {ι : Type*} (W : ι → X.Opens) (hW : ⨆ i, W i = ⊤) :
    Function.Bijective ((modulePullbackPseudofunctor.toDescentData
      (fun i ↦ (W i).ι)).map : (A ⟶ B) → _) := by
  have hcov : ∀ x : X, ∃ i, x ∈ W i := by
    intro x
    have hx : x ∈ (⨆ i, W i : X.Opens) := hW ▸ trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨fun ψ₁ ψ₂ h ↦ ?_, fun D ↦ ?_⟩
  · refine Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_restrict_cover W hcov fun i ↦ ?_
    refine Stacks.AlgebraicGeometry.ModuleLimits.map_eq_of_natIso
      (Scheme.Modules.restrictFunctorIsoPullback (W i).ι).symm ?_
    exact congrFun (congrArg Pseudofunctor.DescentData.Hom.hom h) i
  · have hc : ∀ i j (V : X.Opens) (hVi : V ≤ W i) (hVj : V ≤ W j),
        localApp (restrictHomOfPullbackHom (W i).ι (D.hom i)) V hVi =
          localApp (restrictHomOfPullbackHom (W j).ι (D.hom j)) V hVj := by
      intro i j V hVi hVj
      have hcompat := ((Pseudofunctor.DescentData.subtypeCompatibleHomEquiv
        modulePullbackPseudofunctor (fun i ↦ (W i).ι)).symm D).property i j (Over.mk V.ι)
        (Over.homMk (X.homOfLE hVi) (Scheme.homOfLE_ι X hVi))
        (Over.homMk (X.homOfLE hVj) (Scheme.homOfLE_ι X hVj))
        (by apply Over.OverMorphism.ext; simp)
      rw [localApp_restrictLocal _ hVi, localApp_restrictLocal _ hVj]
      refine (congrArg (fun k ↦ localApp k V le_rfl)
          (restrictLocal_restrictHomOfPullbackHom hVi (D.hom i))).trans
        (Eq.trans ?_ (congrArg (fun k ↦ localApp k V le_rfl)
          (restrictLocal_restrictHomOfPullbackHom hVj (D.hom j))).symm)
      exact congrArg (fun k ↦ localApp (restrictHomOfPullbackHom V.ι k) V le_rfl) hcompat
    obtain ⟨ψ, hψ⟩ := exists_hom_of_localHoms hW _ hc
    refine ⟨ψ, Pseudofunctor.DescentData.hom_ext fun i ↦ ?_⟩
    refine restrictHomOfPullbackHom_injective (W i).ι ?_
    exact (restrictHomOfPullbackHom_map (W i).ι ψ).trans (hψ i)

end Gluing

section Zariski

/-- The sieve generated by a family of open immersions is the sieve generated by the inclusions
of their open ranges. -/
lemma sieve_generate_opensRange {X : Scheme.{u}} {ι : Type*} {U : ι → Scheme.{u}}
    (u : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (u i)] :
    Sieve.generate (Presieve.ofArrows U u) =
      Sieve.generate (Presieve.ofArrows (fun i ↦ ((u i).opensRange).toScheme)
        (fun i ↦ ((u i).opensRange).ι)) := by
  refine le_antisymm ?_ ?_
  · rw [Sieve.generate_le_iff]
    rintro Y f ⟨i⟩
    exact ⟨_, (u i).isoOpensRange.hom, _, Presieve.ofArrows.mk i,
      Scheme.Hom.isoOpensRange_hom_ι (u i)⟩
  · rw [Sieve.generate_le_iff]
    rintro Y f ⟨i⟩
    exact ⟨_, (u i).isoOpensRange.inv, _, Presieve.ofArrows.mk i,
      Scheme.Hom.isoOpensRange_inv_comp (u i)⟩

/-- **The pullback pseudofunctor of sheaves of modules satisfies the descent of morphisms for
every Zariski covering family.** -/
theorem isPrestackFor_zariski (X : Scheme.{u}) (R : Presieve X)
    (hR : R ∈ Scheme.zariskiPrecoverage.{u} X) :
    modulePullbackPseudofunctor.IsPrestackFor R := by
  obtain ⟨ι, U, u, rfl⟩ := R.exists_eq_ofArrows
  have hu : (∀ x : X, ∃ i, x ∈ Set.range (u i)) ∧ ∀ i, IsOpenImmersion (u i) := by simpa using hR
  have := hu.2
  rw [Pseudofunctor.isPrestackFor_iff_of_sieve_eq modulePullbackPseudofunctor
      (sieve_generate_opensRange u),
    Pseudofunctor.isPrestackFor_ofArrows_iff,
    Functor.FullyFaithful.nonempty_iff_map_bijective]
  intro A B
  refine bijective_toDescentData_map_opens (fun i ↦ (u i).opensRange) ?_
  refine eq_top_iff.mpr fun x _ ↦ ?_
  obtain ⟨i, hi⟩ := hu.1 x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩

/-- Morphisms of sheaves of modules glue along Zariski coverings. -/
theorem zariskiModuleHomAmalgamation : ZariskiModuleHomAmalgamation.{u} := by
  intro X ι U u hu A B x hx
  have h := isPrestackFor_zariski X _ hu
  rw [Pseudofunctor.isPrestackFor_ofArrows_iff,
    Functor.FullyFaithful.nonempty_iff_map_bijective] at h
  obtain ⟨t, ht, -⟩ := (Pseudofunctor.bijective_toDescentData_map_iff
    (F := modulePullbackPseudofunctor) u A B).mp (h A B) x hx
  exact ⟨t, ht⟩

/-- The pullback pseudofunctor of sheaves of modules is a prestack for the Zariski topology. -/
theorem isPrestack_zariski : modulePullbackPseudofunctor.IsPrestack Scheme.zariskiTopology.{u} :=
  isPrestack_zariski_of_amalgamation zariskiModuleHomAmalgamation

/-- For every scheme `S` and all sheaves of modules `M` and `N` on `S`, the presheaf on the
schemes over `S` sending `T ⟶ S` to the morphisms `T^* M ⟶ T^* N` is a sheaf for the Zariski
topology. -/
theorem isSheaf_presheafHom_zariski {S : Scheme.{u}} (M N : S.Modules) :
    Presheaf.IsSheaf (Scheme.zariskiTopology.{u}.over S)
      (modulePullbackPseudofunctor.presheafHom M N) :=
  isSheaf_presheafHom_zariski_of_amalgamation zariskiModuleHomAmalgamation M N

/-- The presheaf of morphisms satisfies the sheaf condition for every Zariski covering
family. -/
theorem isSheafFor_presheafHom_zariski' {X : Scheme.{u}} {ι : Type (u + 1)}
    {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ X)
    (hu : Presieve.ofArrows U u ∈ Scheme.zariskiPrecoverage.{u} X) (A B : X.Modules) :
    Presieve.IsSheafFor (modulePullbackPseudofunctor.presheafHom A B) (overPresieve u) :=
  isSheafFor_presheafHom_zariski zariskiModuleHomAmalgamation u hu A B

/-- The pullback-sections presheaf of a quasi-coherent module satisfies the sheaf condition for
the Zariski topology on the schemes over `S`. -/
@[stacks 03DT "Zariski covering"]
theorem quasiCoherentPresheaf_isSheaf_zariski' (S : Scheme.{u}) (F : S.Modules)
    [F.IsQuasicoherent] :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over S) (quasiCoherentPresheafFunctor S F) :=
  Presheaf.isSheaf_of_isSheaf_comp (Scheme.zariskiTopology.over S)
    (quasiCoherentPresheafFunctor S F) (CategoryTheory.forget AddCommGrpCat)
    ((Presheaf.isSheaf_of_iso_iff (quasiCoherentPresheafIsoPresheafHom F)).mpr
      (isSheaf_presheafHom_zariski (Scheme.unitModule S) F))

end Zariski

end AlgebraicGeometry
