module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushforwardSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangePaste

/-!
# The direct image as a functor of stacks of coherent sheaves

Let `π : X ⟶ Y` be a morphism of algebraic spaces over an algebraic space `B`, both of finite
presentation over `B`, and assume that for every object `(T, ℱ)` of `Coh_{X/B}`

* (a) `(T, π_{T,*}ℱ)` is an object of `Coh_{Y/B}`, and
* (b) for a morphism `h : T ⟶ T'` of test schemes and an object `(T', ℱ')`, the base change map
  `Y_h^* π_{T',*} ℱ' ⟶ π_{T,*} X_h^* ℱ'` is an isomorphism.

Then `(T, ℱ) ↦ (T, π_{T,*}ℱ)` is a functor `Coh_{X/B} ⥤ Coh_{Y/B}` lying over the identity of the
test schemes over `B`, and a 1-morphism of categories over the big fppf site.  A morphism
`(h, φ)`, with `φ : X_h^* ℱ' ⟶ ℱ`, is sent to `(h, θ_h ≫ π_{T,*} φ)`, where `θ_h` is the base
change map of the cartesian square of
`AlgebraicGeometry.Space.CoherentPushforwardSituation.isPullback_relativeMap`.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.IsCoherentModule`: the four conditions of
  Stacks 08KB on a module over a base change.
* `AlgebraicGeometry.Space.CoherentPushforwardSituation.baseChange`: the base change map
  `θ_h : Y_h^* π_{T',*} ⟶ π_{T,*} X_h^*`.
* `AlgebraicGeometry.Space.CoherentPushforwardSituation.PreservesCoherence`: conditions (a) and
  (b).
* `AlgebraicGeometry.Space.CoherentPushforwardSituation.pushforwardObject` and
  `AlgebraicGeometry.Space.CoherentPushforwardSituation.pushforwardHom`: the action on objects and
  on morphisms.
* `AlgebraicGeometry.Space.CoherentPushforwardSituation.pushforwardFunctor`: the functor
  `Coh_{X/B} ⥤ Coh_{Y/B}`, and
  `AlgebraicGeometry.Space.CoherentPushforwardSituation.pushforwardBased`: the same as a
  1-morphism of categories over the big fppf site.

## Main results

* `AlgebraicGeometry.Space.CoherentPushforwardSituation.pushforwardFibre_fibreComp`: the direct
  image carries composites of fibre morphisms, along the comparisons of Stacks 03LU for a
  composite of test schemes, to composites.
* `AlgebraicGeometry.Space.CoherentPushforwardSituation.pushforwardHom_comp` and
  `AlgebraicGeometry.Space.CoherentPushforwardSituation.pushforwardHom_id`: functoriality.
* `AlgebraicGeometry.Space.CoherentPushforwardSituation.pushforwardFunctor_comp_projection`: the
  functor lies over the identity of the test schemes over `B`.

## References

* [Stacks Project, Tag 0DN9](https://stacks.math.columbia.edu/tag/0DN9)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 08W5](https://stacks.math.columbia.edu/tag/08W5)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Functor

/-- The conjugate of a fibre morphism by a natural transformation between iterated functors.

Let `Lp : 𝒜₁ ⥤ 𝒜₀` and `Lq : ℬ₁ ⥤ ℬ₀` be two "horizontal" functors, `E₀ : 𝒜₀ ⥤ ℬ₀` and
`E₁ : 𝒜₁ ⥤ ℬ₁` two "vertical" ones, and `σ : E₁ ⋙ Lq ⟶ Lp ⋙ E₀` a transformation between the two
ways round the square.  A fibre morphism `φ : Lp.obj M' ⟶ M` has the conjugate
`Lq.obj (E₁.obj M') ⟶ E₀.obj M`: apply `E₀` to it and precompose with the component of `σ`. -/
def conjFibreHom {𝒜₀ : Type*} {𝒜₁ : Type*} {ℬ₀ : Type*} {ℬ₁ : Type*} [Category* 𝒜₀]
    [Category* 𝒜₁] [Category* ℬ₀] [Category* ℬ₁] {Lp : 𝒜₁ ⥤ 𝒜₀} {E₀ : 𝒜₀ ⥤ ℬ₀}
    {E₁ : 𝒜₁ ⥤ ℬ₁} {Lq : ℬ₁ ⥤ ℬ₀} (σ : E₁ ⋙ Lq ⟶ Lp ⋙ E₀) {M : 𝒜₀} {M' : 𝒜₁}
    (φ : Lp.obj M' ⟶ M) : Lq.obj (E₁.obj M') ⟶ E₀.obj M :=
  σ.app M' ≫ E₀.map φ

/-- The conjugate of an isomorphism by a transformation invertible at the relevant object is an
isomorphism. -/
theorem isIso_conjFibreHom {𝒜₀ : Type*} {𝒜₁ : Type*} {ℬ₀ : Type*} {ℬ₁ : Type*} [Category* 𝒜₀]
    [Category* 𝒜₁] [Category* ℬ₀] [Category* ℬ₁] {Lp : 𝒜₁ ⥤ 𝒜₀} {E₀ : 𝒜₀ ⥤ ℬ₀}
    {E₁ : 𝒜₁ ⥤ ℬ₁} {Lq : ℬ₁ ⥤ ℬ₀} (σ : E₁ ⋙ Lq ⟶ Lp ⋙ E₀) {M : 𝒜₀} {M' : 𝒜₁}
    (φ : Lp.obj M' ⟶ M) (hσ : IsIso (σ.app M')) (hφ : IsIso φ) : IsIso (conjFibreHom σ φ) :=
  inferInstanceAs (IsIso (σ.app M' ≫ E₀.map φ))

/-- **Conjugating composites of fibre morphisms by pasted base change maps, abstractly.**  Let
`θ₁ : E₁ ⋙ Lq₁ ⟶ Lp₁ ⋙ E₀` and `θ₂ : E₂ ⋙ Lq₂ ⟶ Lp₂ ⋙ E₁` be the base change maps of two stacked
squares, `θ'` the base change map of the outer rectangle with horizontal functors `Lq'`, `Lp'`
compared with the composites by `cY`, `cX`, and suppose `θ'` is the pasting of `θ₁` and `θ₂`.  Let
`θ` be `θ'` transported along identifications `eY : Lq = Lq'`, `eX : Lp = Lp'`, and let `τY`, `τX`
be the resulting comparisons of `Lq`, `Lp` with the composites.  Then conjugating by the base
change maps carries a composite of fibre morphisms along `τX` to the composite of the conjugates
along `τY`. -/
theorem fibreComp_baseChange {A₀ A₁ A₂ B₀ B₁ B₂ : Type*} [Category* A₀] [Category* A₁]
    [Category* A₂] [Category* B₀] [Category* B₁] [Category* B₂] {E₀ : A₀ ⥤ B₀} {E₁ : A₁ ⥤ B₁}
    {E₂ : A₂ ⥤ B₂} {Lq₁ : B₁ ⥤ B₀} {Lq₂ : B₂ ⥤ B₁} {Lq Lq' : B₂ ⥤ B₀} {Lp₁ : A₁ ⥤ A₀}
    {Lp₂ : A₂ ⥤ A₁} {Lp Lp' : A₂ ⥤ A₀} (θ₁ : E₁ ⋙ Lq₁ ⟶ Lp₁ ⋙ E₀) (θ₂ : E₂ ⋙ Lq₂ ⟶ Lp₂ ⋙ E₁)
    (θ : E₂ ⋙ Lq ⟶ Lp ⋙ E₀) (θ' : E₂ ⋙ Lq' ⟶ Lp' ⋙ E₀) (cY : Lq₂ ⋙ Lq₁ ≅ Lq')
    (cX : Lp₂ ⋙ Lp₁ ≅ Lp') (eY : Lq = Lq') (eX : Lp = Lp') (τY : Lq ≅ Lq₂ ⋙ Lq₁)
    (τX : Lp ≅ Lp₂ ⋙ Lp₁) (hτY : τY = eqToIso eY ≪≫ cY.symm) (hτX : τX = eqToIso eX ≪≫ cX.symm)
    (hθ : HEq θ θ')
    (hpaste : ∀ K : A₂, θ'.app K = cY.inv.app (E₂.obj K) ≫ Lq₁.map (θ₂.app K) ≫
      θ₁.app (Lp₂.obj K) ≫ E₀.map (cX.hom.app K))
    {M : A₀} {M' : A₁} {M'' : A₂} (φ : Lp₁.obj M' ⟶ M) (ψ : Lp₂.obj M'' ⟶ M') :
    conjFibreHom θ (fibreComp τX φ ψ) =
      fibreComp τY (conjFibreHom θ₁ φ) (conjFibreHom θ₂ ψ) := by
  subst hτY hτX eY eX
  unfold conjFibreHom
  have hc : θ.app M'' = θ'.app M'' := by rw [eq_of_heq hθ]
  have hn := θ₁.naturality ψ
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  simp only [fibreComp, eqToIso_refl, Iso.refl_trans, Iso.symm_hom, Functor.map_comp,
    Category.assoc]
  rw [hc, hpaste M'']
  simp only [Category.assoc]
  rw [reassoc_of% hn, ← Functor.map_comp_assoc E₀ (cX.hom.app M'') (cX.inv.app M''),
    Iso.hom_inv_id_app]
  simp

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CoherentSituation

variable (D : CoherentSituation B S hS)

/-- The four conditions of Stacks 08KB on an `𝒪_{X_T}`-module: it is quasi-coherent, of finite
presentation, flat over the test scheme and its support is a closed subset proper over the test
scheme.  These are exactly the conditions on the module of an object of `Coh_{X/Y}`. -/
structure IsCoherentModule (T : SchemesOver D.Y)
    (F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) : Prop where
  /-- It is quasi-coherent (Stacks 03G9). -/
  quasicoherent : F.IsQuasicoherentOnSite
  /-- It is of finite presentation (Stacks 03DL). -/
  finitePresentation : F.IsFinitePresentationOnSite
  /-- It is flat over the test scheme (Stacks 05VV). -/
  flat : IsFlatOver B S hS (D.space T).2 (D.projection T).hom F
  /-- Its support is a closed subset proper over the test scheme (Stacks 0CZD). -/
  properSupport : ∃ (hp : IsLocallyOfFiniteType B S hS (D.projection T).hom)
      (hU : IsClosed (D.support T F)),
      IsProperOver B S hS (D.space T).2
        ((schemeSpaceFunctor B S hS).obj T.left).2 (D.projection T).hom hp (D.support T F) hU

/-- The object of `Coh_{X/Y}` given by a test scheme and a module satisfying the four conditions
of Stacks 08KB. -/
@[simps]
def IsCoherentModule.toObject {T : SchemesOver D.Y}
    {F : Modules.{u, u} B S hS (D.space T).1 (D.space T).2} (h : D.IsCoherentModule T F) :
    CoherentObject D :=
  ⟨T, F, h.quasicoherent, h.finitePresentation, h.flat, h.properSupport⟩

end CoherentSituation

/-- The module of an object of `Coh_{X/Y}` satisfies the four conditions of Stacks 08KB. -/
theorem CoherentObject.isCoherentModule {D : CoherentSituation B S hS} (A : CoherentObject D) :
    D.IsCoherentModule A.T A.F :=
  ⟨A.quasicoherent, A.finitePresentation, A.flat, A.properSupport⟩

/-- The base change maps of two squares whose horizontal morphisms are equal are heterogeneously
equal. -/
theorem moduleBaseChangeMap_heq {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (f' : X' ⟶ Y')
    {g₁ g₂ : Y' ⟶ Y} {g₁' g₂' : X' ⟶ X} (p : g₁ = g₂) (p' : g₁' = g₂')
    (w₁ : g₁' ≫ f = f' ≫ g₁) (w₂ : g₂' ≫ f = f' ≫ g₂) :
    HEq (moduleBaseChangeMap f g₁ f' g₁' w₁) (moduleBaseChangeMap f g₂ f' g₂' w₂) := by
  subst p p'
  rfl

namespace CoherentPushforwardSituation

variable (D : CoherentPushforwardSituation B S hS)

/-! ### The base change maps -/

/-- **The base change map `θ_h : Y_h^* π_{T',*} ⟶ π_{T,*} X_h^*`** of the cartesian square of
`AlgebraicGeometry.Space.CoherentPushforwardSituation.isPullback_relativeMap`, for a morphism
`h : T ⟶ T'` of test schemes over `B`. -/
abbrev baseChange {T T' : SchemesOver D.base} (h : T ⟶ T') :
    modulePushforward B S hS (D.mapAt T') ⋙ modulePullback B S hS (D.target.relativeMap h) ⟶
      modulePullback B S hS (D.source.relativeMap h) ⋙ modulePushforward B S hS (D.mapAt T) :=
  moduleBaseChangeMap (D.mapAt T') (D.target.relativeMap h) (D.mapAt T)
    (D.source.relativeMap h) (D.relativeMap_comp_mapAt h)

/-- **The fibre morphism `θ_h ≫ π_{T,*}φ`** carried by the direct image: for a morphism
`h : T ⟶ T'` of test schemes and `φ : X_h^* ℱ' ⟶ ℱ`, the morphism
`Y_h^* π_{T',*} ℱ' ⟶ π_{T,*} X_h^* ℱ' ⟶ π_{T,*} ℱ`. -/
abbrev pushforwardFibre {T T' : SchemesOver D.base} (h : T ⟶ T')
    {F : Modules.{u, u} B S hS (D.source.space T).1 (D.source.space T).2}
    {F' : Modules.{u, u} B S hS (D.source.space T').1 (D.source.space T').2}
    (φ : (modulePullback B S hS (D.source.relativeMap h)).obj F' ⟶ F) :
    (modulePullback B S hS (D.target.relativeMap h)).obj
        ((modulePushforward B S hS (D.mapAt T')).obj F') ⟶
      (modulePushforward B S hS (D.mapAt T)).obj F :=
  Functor.conjFibreHom (D.baseChange h) φ

/-- **The direct image carries composites of fibre morphisms to composites.**  For
`h : T ⟶ T'`, `h' : T' ⟶ T''` and fibre morphisms `φ : X_h^* ℱ' ⟶ ℱ`, `ψ : X_{h'}^* ℱ'' ⟶ ℱ'`,
the fibre morphism carried by their composite along the comparison of Stacks 03LU for
`X_{h ≫ h'}` is the composite of the carried fibre morphisms along the comparison for
`Y_{h ≫ h'}`. -/
theorem pushforwardFibre_fibreComp {T T' T'' : SchemesOver D.base} (h : T ⟶ T')
    (h' : T' ⟶ T'') {F : Modules.{u, u} B S hS (D.source.space T).1 (D.source.space T).2}
    {F' : Modules.{u, u} B S hS (D.source.space T').1 (D.source.space T').2}
    {F'' : Modules.{u, u} B S hS (D.source.space T'').1 (D.source.space T'').2}
    (φ : (modulePullback B S hS (D.source.relativeMap h)).obj F' ⟶ F)
    (ψ : (modulePullback B S hS (D.source.relativeMap h')).obj F'' ⟶ F') :
    D.pushforwardFibre (h ≫ h') (Functor.fibreComp (D.source.compComparison h h') φ ψ) =
      Functor.fibreComp (D.target.compComparison h h') (D.pushforwardFibre h φ)
        (D.pushforwardFibre h' ψ) := by
  have hY : D.target.relativeMap h ≫ D.target.relativeMap h' =
      D.target.relativeMap (h ≫ h') := (baseChangeMap_comp D.f h h').symm
  have hX : D.source.relativeMap h ≫ D.source.relativeMap h' =
      D.source.relativeMap (h ≫ h') :=
    (baseChangeMap_comp (D.π ≫ D.f) h h').symm
  have hw := pasteBaseComm _ _ _ _ _ _ _ (D.relativeMap_comp_mapAt h')
    (D.relativeMap_comp_mapAt h)
  exact Functor.fibreComp_baseChange (D.baseChange h) (D.baseChange h')
    (D.baseChange (h ≫ h'))
    (moduleBaseChangeMap (D.mapAt T'') (D.target.relativeMap h ≫ D.target.relativeMap h')
      (D.mapAt T) (D.source.relativeMap h ≫ D.source.relativeMap h') hw)
    (modulePullbackCompIso B S hS (D.target.relativeMap h) (D.target.relativeMap h'))
    (modulePullbackCompIso B S hS (D.source.relativeMap h) (D.source.relativeMap h'))
    (congrArg (modulePullback B S hS) hY.symm) (congrArg (modulePullback B S hS) hX.symm)
    (D.target.compComparison h h') (D.source.compComparison h h') rfl rfl
    (moduleBaseChangeMap_heq (D.mapAt T'') (D.mapAt T) hY.symm hX.symm _ hw)
    (fun K => moduleBaseChangeMap_paste (D.mapAt T'') (D.target.relativeMap h')
      (D.mapAt T') (D.source.relativeMap h') (D.target.relativeMap h) (D.mapAt T)
      (D.source.relativeMap h) (D.relativeMap_comp_mapAt h')
      (D.relativeMap_comp_mapAt h) hw K) φ ψ

/-! ### Conditions (a) and (b) -/

/-- **The direct image preserves coherence**: (a) for every object `(T, ℱ)` of `Coh_{X/B}` the
direct image `π_{T,*}ℱ` satisfies the four conditions of Stacks 08KB, and (b) the base change map
`θ_h` is an isomorphism at the module of every object of `Coh_{X/B}`. -/
structure PreservesCoherence : Prop where
  /-- The direct image of the module of an object of `Coh_{X/B}` is the module of an object of
  `Coh_{Y/B}`. -/
  isCoherentModule : ∀ A : CoherentObject D.source,
    D.target.IsCoherentModule A.T ((modulePushforward B S hS (D.mapAt A.T)).obj A.F)
  /-- The base change map is an isomorphism at the module of an object of `Coh_{X/B}`. -/
  isIso_baseChange : ∀ (A : CoherentObject D.source) {T : SchemesOver D.base} (h : T ⟶ A.T),
    IsIso ((D.baseChange h).app A.F)

variable {D} (H : D.PreservesCoherence)

/-! ### The functor -/

/-- **The object `(T, π_{T,*}ℱ)` of `Coh_{Y/B}`** attached to an object `(T, ℱ)` of
`Coh_{X/B}`. -/
def pushforwardObject (A : CoherentObject D.source) : CoherentObject D.target :=
  (H.isCoherentModule A).toObject

/-- The image of an object keeps its test scheme. -/
@[simp]
theorem pushforwardObject_T (A : CoherentObject D.source) : (pushforwardObject H A).T = A.T :=
  rfl

/-- The module of the image of an object `(T, ℱ)` is `π_{T,*}ℱ`. -/
@[simp]
theorem pushforwardObject_F (A : CoherentObject D.source) :
    (pushforwardObject H A).F = (modulePushforward B S hS (D.mapAt A.T)).obj A.F :=
  rfl

/-- **The morphism `(h, θ_h ≫ π_{T,*}φ)` of `Coh_{Y/B}`** attached to a morphism `(h, φ)` of
`Coh_{X/B}`. -/
def pushforwardHom {A A' : CoherentObject D.source} (m : CoherentHom A A') :
    CoherentHom (pushforwardObject H A) (pushforwardObject H A') where
  base := m.base
  fibre := D.pushforwardFibre m.base m.fibre
  isIso_fibre := Functor.isIso_conjFibreHom _ _ (H.isIso_baseChange A' m.base) m.isIso_fibre

/-- The image of a morphism keeps its morphism of test schemes. -/
@[simp]
theorem pushforwardHom_base {A A' : CoherentObject D.source} (m : CoherentHom A A') :
    (pushforwardHom H m).base = m.base :=
  rfl

/-- The fibre morphism of the image of a morphism `(h, φ)` is `θ_h ≫ π_{T,*}φ`. -/
theorem pushforwardHom_fibre {A A' : CoherentObject D.source} (m : CoherentHom A A') :
    (pushforwardHom H m).fibre = D.pushforwardFibre m.base m.fibre :=
  rfl

/-- The base map of the image of a composite. -/
theorem pushforwardHom_comp_base {A A' A'' : CoherentObject D.source} (m : CoherentHom A A')
    (n : CoherentHom A' A'') :
    (pushforwardHom H (m.comp n)).base = ((pushforwardHom H m).comp (pushforwardHom H n)).base :=
  rfl

/-- **The direct image preserves composition.** -/
theorem pushforwardHom_comp {A A' A'' : CoherentObject D.source} (m : CoherentHom A A')
    (n : CoherentHom A' A'') :
    pushforwardHom H (m.comp n) = (pushforwardHom H m).comp (pushforwardHom H n) := by
  refine coherentHom_eq_of_heq (pushforwardHom_comp_base H m n) (heq_of_eq ?_)
  rw [pushforwardHom_fibre H (m.comp n), CoherentHom.comp_fibre (pushforwardHom H m),
    pushforwardHom_fibre H m, pushforwardHom_fibre H n]
  exact D.pushforwardFibre_fibreComp m.base n.base m.fibre n.fibre

/-- **The direct image preserves identities.** -/
theorem pushforwardHom_id (A : CoherentObject D.source) :
    pushforwardHom H (CoherentHom.id (modulePushforwardCoherence B S hS) A) =
      CoherentHom.id (modulePushforwardCoherence B S hS) (pushforwardObject H A) := by
  let : Category.{u + 1} (CoherentObject D.target) := D.target.categoryData.category
  let e : pushforwardObject H A ⟶ pushforwardObject H A :=
    pushforwardHom H (CoherentHom.id (modulePushforwardCoherence B S hS) A)
  have hidem : e ≫ e = e := by
    show (pushforwardHom H _).comp (pushforwardHom H _) = pushforwardHom H _
    rw [← pushforwardHom_comp, CoherentHom.id_comp]
  have hlift : (D.target.categoryData.projection ⋙
      CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.target.Y).IsHomLift
        (𝟙 A.T.left) e := by
    have : (D.target.categoryData.projection ⋙
        CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.target.Y).map e = 𝟙 A.T.left := rfl
    exact this ▸ Functor.IsHomLift.map (p := _) e
  have hiso : IsIso e :=
    Functor.isIso_of_isHomLift_id' _ D.target.projection_isFiberedInGroupoids e hlift
  have : e = 𝟙 _ := by
    rw [← cancel_epi e, hidem, Category.comp_id]
  exact this

/-- **The functor `Coh_{X/B} ⥤ Coh_{Y/B}` induced by the direct image**, for a direct image
preserving coherence: `(T, ℱ) ↦ (T, π_{T,*}ℱ)`. -/
def pushforwardFunctor :
    @Functor (CoherentObject D.source) D.source.categoryData.category
      (CoherentObject D.target) D.target.categoryData.category :=
  letI : Category.{u + 1} (CoherentObject D.source) := D.source.categoryData.category
  letI : Category.{u + 1} (CoherentObject D.target) := D.target.categoryData.category
  { obj := pushforwardObject H
    map := fun m ↦ pushforwardHom H m
    map_id := fun A ↦ pushforwardHom_id H A
    map_comp := fun m n ↦ pushforwardHom_comp H m n }

/-- The functor sends an object to `pushforwardObject`. -/
@[simp]
theorem pushforwardFunctor_obj (A : CoherentObject D.source) :
    letI : Category.{u + 1} (CoherentObject D.source) := D.source.categoryData.category
    letI : Category.{u + 1} (CoherentObject D.target) := D.target.categoryData.category
    (pushforwardFunctor H).obj A = pushforwardObject H A :=
  rfl

/-- **The functor lies over the identity of the test schemes over `B`.** -/
theorem pushforwardFunctor_comp_projection :
    letI : Category.{u + 1} (CoherentObject D.source) := D.source.categoryData.category
    letI : Category.{u + 1} (CoherentObject D.target) := D.target.categoryData.category
    pushforwardFunctor H ⋙ D.target.categoryData.projection = D.source.categoryData.projection :=
  rfl

/-- **The direct image as a 1-morphism `Coh_{X/B} ⟶ Coh_{Y/B}` of categories over the big fppf
site**, for a direct image preserving coherence. -/
def pushforwardBased :
    coherentBasedCategory D.source.categoryData ⥤ᵇ coherentBasedCategory D.target.categoryData where
  toFunctor := pushforwardFunctor H
  w := rfl

/-- The 1-morphism commutes with the projections to `𝒮_B` which forget the module. -/
theorem pushforwardBased_comp_coherentToBase :
    (pushforwardBased H).toFunctor ⋙ (coherentToBase D.target.categoryData).toFunctor =
      (coherentToBase D.source.categoryData).toFunctor :=
  rfl

end CoherentPushforwardSituation

end AlgebraicGeometry.Space

end
