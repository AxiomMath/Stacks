module

public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralization
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaProductsToDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomSpaceLocallyOfFiniteType
public import StacksFrontier.Deformation.ArtinCriteria.BaseChangeSections
import all StacksFrontier.Deformation.ArtinCriteria.BaseChangeSections
import all StacksFrontier.Deformation.ArtinCriteria.VersalBaseChange

/-!
# The smooth locus of a base change of a versal object

Let `𝒳` be a category fibred in groupoids over the big fppf site of a locally Noetherian scheme
`S`, with representable diagonal, satisfying (RS*) and limit preserving. Let `x` be an object of
`𝒳` over `U`, versal at a finite type point `u₀`, and let `x ⟶ x'` be an arrow over a morphism
`g : U ⟶ U'` of schemes locally of finite type over `S`. Form the algebraic space `Z` over `U'`
representing `(Sch/U') ×_{x', 𝒳, x} (Sch/U)`; the arrow `x ⟶ x'` is a section `s₀` of `Z` over
`U`. By Stacks 0CXM, `Z ⟶ U'` is smooth at the image of `u₀`, hence on an open subspace `Z₀`;
this file records that open subspace together with the facts the proof of Stacks 0G2K uses:
`s₀` is the canonical point, and it sends every generization of `u₀` into `Z₀`.

## Main results

* `Deformation.Artin.BaseChange.exists_smooth_openSubspace_of_isVersalAt`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace Deformation.Artin.BaseChange

universe u v w

attribute [local implicit_reducible] CategoryTheory.Functor.TwoYoneda.liftBased
  CategoryTheory.Functor.TwoYoneda.liftFunctor
  CategoryTheory.TwoFibreProductOver.fst
  CategoryTheory.BasedCategory.ofFunctor

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (AlgebraicGeometry.BigFppfOver B S hS))

/-- The 2-Yoneda functor of an object `x'` over `U'`, on the big fppf site over `U'`. -/
abbrev twoYoneda (U' : AlgebraicGeometry.BigFppfOver B S hS) (x' : 𝒳.val.obj)
    (hx' : 𝒳.val.p.obj x' = U') :
    AlgebraicGeometry.BigFppfOver B U'.left.1 U'.left.2 ⥤ 𝒳.val.obj :=
  Over.iteratedSliceBackward U' ⋙
    (Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.isFiberedInGroupoids U' ⟨x', hx'⟩).toFunctor

/-- The 2-Yoneda functor of `x'` followed by the projection of `𝒳` is the functor
`Over.map U'.hom` forgetting to the big fppf site over `S`. -/
theorem twoYoneda_comp (U' : AlgebraicGeometry.BigFppfOver B S hS) (x' : 𝒳.val.obj)
    (hx' : 𝒳.val.p.obj x' = U') :
    twoYoneda B S hS 𝒳 U' x' hx' ⋙ 𝒳.val.p = Over.map U'.hom := by
  have h := Functor.TwoYoneda.liftFunctor_w 𝒳.val.p 𝒳.isFiberedInGroupoids U' ⟨x', hx'⟩
  exact congrArg (fun G => Over.iteratedSliceBackward U' ⋙ G) h

/-- `U` read as an object of the big fppf site over `U'` through `g : U ⟶ U'`. -/
abbrev overObj {U U' : AlgebraicGeometry.BigFppfOver B S hS} (g : U ⟶ U') :
    AlgebraicGeometry.BigFppfOver B U'.left.1 U'.left.2 :=
  Over.mk g.left

/-- `U` read through `g : U ⟶ U'` and pushed back along `U' ⟶ S` is `U`. -/
theorem overMap_overObj {U U' : AlgebraicGeometry.BigFppfOver B S hS} (g : U ⟶ U') :
    (Over.map U'.hom).obj (overObj B S hS g) = U := by
  change Over.mk (g.left ≫ U'.hom) = U
  rw [Over.w g]
  rfl

/-- The base of the canonical point: `U` itself, read through `g`. -/
abbrev canonicalBase {U U' : AlgebraicGeometry.BigFppfOver B S hS} (g : U ⟶ U') :
    AlgebraicGeometry.BigFppfOver B S hS :=
  (Over.map U'.hom).obj (overObj B S hS g)

/-- The arrow of `U` read through `g` to `U`. -/
abbrev canonicalSlice {U U' : AlgebraicGeometry.BigFppfOver B S hS} (g : U ⟶ U') : Over U :=
  Over.mk (eqToHom (overMap_overObj B S hS g))

/-- The chosen arrow `cartArrow` of the 2-Yoneda functor of `x` is cartesian over `a.hom`. -/
theorem cartArrow_isCartesian (U : AlgebraicGeometry.BigFppfOver B S hS) (x : 𝒳.val.obj)
    (hx : 𝒳.val.p.obj x = U) (a : Over U) :
    𝒳.val.p.IsCartesian a.hom (cartArrow B S hS 𝒳 U x hx a) :=
  have := (Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.isFiberedInGroupoids U ⟨x, hx⟩
    a).isStronglyCartesian
  inferInstance

/-- The chosen arrow `cartArrow` of the 2-Yoneda functor of `x` lies over `a.hom`. -/
private theorem cartArrow_isHomLift (U : AlgebraicGeometry.BigFppfOver B S hS) (x : 𝒳.val.obj)
    (hx : 𝒳.val.p.obj x = U) (a : Over U) :
    𝒳.val.p.IsHomLift a.hom (cartArrow B S hS 𝒳 U x hx a) :=
  (cartArrow_isCartesian B S hS 𝒳 U x hx a).toIsHomLift

/-- Two arrows of a category fibred in groupoids over one morphism of the base into one object
differ by a unique vertical isomorphism. -/
theorem exists_vertical_iso {C X : Type*} [Category C] [Category X] (p : X ⥤ C)
    (hp : p.IsFiberedInGroupoids) {R S' : C} (b : R ⟶ S')
    {a z z' : X} (hz : p.obj z = R) (hz' : p.obj z' = R)
    (φ : z ⟶ a) (φ' : z' ⟶ a) [p.IsHomLift b φ] [p.IsHomLift b φ'] :
    ∃ e : z ≅ z', p.IsHomLift (𝟙 R) e.hom ∧ e.hom ≫ φ' = φ := by
  obtain ⟨χ, ⟨hχ1, hχ2⟩, -⟩ := hp.unique_lift φ' φ (eqToHom (hz.trans hz'.symm)) (by
    rw [IsHomLift.fac' p b φ', IsHomLift.fac' p b φ]
    simp)
  have hχl : p.IsHomLift (𝟙 R) χ := IsHomLift.of_fac' p _ χ hz hz' (by
    rw [hχ1]; simp)
  have : p.IsStronglyCartesian (𝟙 R) χ := hp.isStronglyCartesian_homLift _ χ
  have : IsIso χ := Functor.IsStronglyCartesian.isIso_of_base_isIso p (𝟙 R) χ
  exact ⟨asIso χ, hχl, hχ2⟩

/-- The canonical object of the 2-fibre product attached to an arrow `κ : x ⟶ x'` over
`g : U ⟶ U'`: the point `(U ⟶ U', 𝟙 U, x|_U ≅ x'|_U)`, together with its arrow to `x`
composed with `κ`. -/
theorem exists_canonicalPoint {U U' : AlgebraicGeometry.BigFppfOver B S hS} (g : U ⟶ U')
    {x x' : 𝒳.val.obj} (hx : 𝒳.val.p.obj x = U) (hx' : 𝒳.val.p.obj x' = U')
    (κ : x ⟶ x') (hκ : 𝒳.val.p.IsHomLift g κ) :
    ∃ Q : BaseChangeProduct B S hS 𝒳 U U' x hx (twoYoneda B S hS 𝒳 U' x' hx'),
      ∃ hQ : Q.x = overObj B S hS g, Q.y = canonicalSlice B S hS g ∧
      (twoYoneda B S hS 𝒳 U' x' hx').map (eqToHom hQ.symm) ≫
          pointArrow B S hS 𝒳 U U' x hx (twoYoneda B S hS 𝒳 U' x' hx') Q ≫ κ =
        cartArrow B S hS 𝒳 U' x' hx'
          ((Over.iteratedSliceBackward U').obj (overObj B S hS g)) := by
  let L := Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.isFiberedInGroupoids U ⟨x, hx⟩
  let yV := twoYoneda B S hS 𝒳 U' x' hx'
  have hyVobj : 𝒳.val.p.obj (yV.obj (overObj B S hS g)) = canonicalBase B S hS g :=
    Functor.congr_obj (twoYoneda_comp B S hS 𝒳 U' x' hx') (overObj B S hS g)
  have hLobj : 𝒳.val.p.obj (L.obj (canonicalSlice B S hS g)) = canonicalBase B S hS g :=
    Functor.congr_obj (Functor.TwoYoneda.liftFunctor_w 𝒳.val.p 𝒳.isFiberedInGroupoids U
      ⟨x, hx⟩) (canonicalSlice B S hS g)
  have hb : ((Over.iteratedSliceBackward U').obj (overObj B S hS g)).hom =
      (canonicalSlice B S hS g).hom ≫ g := by
    apply Over.OverMorphism.ext
    simp only [canonicalSlice, overObj, Over.comp_left, Over.mk_hom, Over.eqToHom_left]
    simp only [eqToHom_refl, Category.id_comp]
    rfl
  have h2 : 𝒳.val.p.IsHomLift ((Over.iteratedSliceBackward U').obj (overObj B S hS g)).hom
      (cartArrow B S hS 𝒳 U x hx (canonicalSlice B S hS g) ≫ κ) := by
    rw [hb]
    exact @IsHomLift.comp _ _ _ _ 𝒳.val.p _ _ _ _ _ _ _ g _ κ
      (cartArrow_isHomLift B S hS 𝒳 U x hx (canonicalSlice B S hS g)) hκ
  have h1' := cartArrow_isHomLift B S hS 𝒳 U' x' hx'
    ((Over.iteratedSliceBackward U').obj (overObj B S hS g))
  obtain ⟨e, he, hef⟩ := exists_vertical_iso 𝒳.val.p 𝒳.isFiberedInGroupoids
    ((Over.iteratedSliceBackward U').obj (overObj B S hS g)).hom hyVobj hLobj
    (cartArrow B S hS 𝒳 U' x' hx' ((Over.iteratedSliceBackward U').obj (overObj B S hS g)))
    (cartArrow B S hS 𝒳 U x hx (canonicalSlice B S hS g) ≫ κ)
  refine ⟨⟨canonicalBase B S hS g, overObj B S hS g, canonicalSlice B S hS g, rfl, rfl, e, he⟩,
    rfl, rfl, ?_⟩
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp, pointArrow,
    Category.assoc]
  exact hef

/-- **The smooth locus of the base change of a versal object.** Let `x` over `U` be versal at
a finite type point `u₀`, and `κ : x ⟶ x'` an arrow over a morphism `g : U ⟶ U'` of schemes locally
of finite type over `S` which is a monomorphism. The algebraic space `F` over `U'` representing
`(Sch/U') ×_{x', 𝒳, x} (Sch/U)` carries a section `s₀` over `U` whose arrow is `κ`, and an open
subspace `Z₀` smooth over `U'`; the points `u` of `U` which `s₀` sends into `Z₀` form an open
neighbourhood `V` of `u₀`. -/
theorem exists_smooth_openSubspace_isOpen_of_isVersalAt [IsLocallyNoetherian S]
    (hΔ : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS 𝒳)
    (hRS : Deformation.Artin.SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, w, v} B S hS 𝒳)
    {U U' : AlgebraicGeometry.BigFppfOver B S hS} [LocallyOfFiniteType (B.inclusion.map U.hom)]
    [LocallyOfFiniteType (B.inclusion.map U'.hom)] (g : U ⟶ U')
    (hgmono : Mono (B.inclusion.map g.left))
    {x x' : 𝒳.val.obj} (hx : 𝒳.val.p.obj x = U) (hx' : 𝒳.val.p.obj x' = U')
    (κ : x ⟶ x') (hκ : 𝒳.val.p.IsHomLift g κ)
    (u₀ : U.left.1) (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)
    (hversal : Deformation.Artin.IsVersalAt (Over.mk (B.inclusion.map U.hom))
      (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x
      (by simpa using congrArg (Over.post B.inclusion).obj hx)) :
    ∃ (F : (AlgebraicGeometry.BigFppfOver B U'.left.1 U'.left.2)ᵒᵖ ⥤ Type u)
      (_ : AlgebraicGeometry.IsAlgebraicSpace B U'.left.1 U'.left.2 F)
      (e : BaseChangeEquivalence B S hS 𝒳 U U' x hx (twoYoneda B S hS 𝒳 U' x' hx') F)
      (s₀ : F.obj (op (overObj B S hS g))) (Z₀ : Subfunctor F),
      AlgebraicGeometry.Space.IsOpenSubspace B U'.left.1 U'.left.2 Z₀ ∧
      AlgebraicGeometry.Space.IsSmooth B U'.left.1 U'.left.2 (Z₀.ι ≫ terminal.from F) ∧
      sectionArrow B S hS 𝒳 U U' x hx (twoYoneda B S hS 𝒳 U' x' hx') F e
          ⟨overObj B S hS g, Discrete.mk s₀⟩ ≫ κ =
        cartArrow B S hS 𝒳 U' x' hx' ((Over.iteratedSliceBackward U').obj (overObj B S hS g)) ∧
      ∃ V : Set ((AlgebraicGeometry.BigFppfOver.toScheme B U'.left.1 U'.left.2).obj
          (overObj B S hS g)), IsOpen V ∧ u₀ ∈ V ∧
        ∀ (Y : AlgebraicGeometry.BigFppfOver B U'.left.1 U'.left.2) (h : Y ⟶ overObj B S hS g),
          (∀ y, (AlgebraicGeometry.BigFppfOver.toScheme B U'.left.1 U'.left.2).map h y ∈ V) →
          ∃ α : yoneda.obj Y ⟶ Z₀.toFunctor, α ≫ Z₀.ι = yoneda.map h ≫ yonedaEquiv.symm s₀ := by
  classical
  let p := 𝒳.val.p
  have hp := 𝒳.isFiberedInGroupoids
  let : p.IsFibered := hp.isFibered
  let yV := twoYoneda B S hS 𝒳 U' x' hx'
  have hyV : yV ⋙ p = Over.map U'.hom := twoYoneda_comp B S hS 𝒳 U' x' hx'
  -- the representing algebraic space
  let f₀ : (AlgebraicGeometry.Stack.schemeFibredCategory B S hS U).val ⥤ᵇ 𝒳.val :=
    Functor.TwoYoneda.liftBased p hp U ⟨x, hx⟩
  have hrep := (AlgebraicGeometry.Stack.isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes
    B S hS 𝒳).mp ((AlgebraicGeometry.Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf
      B S hS 𝒳).mp hΔ) U f₀
  obtain ⟨F, hF, ⟨eF⟩⟩ := hrep U' yV hyV
  let e : BaseChangeEquivalence B S hS 𝒳 U U' x hx yV F := eF
  -- the canonical section over `U`
  obtain ⟨Q, hQx, -, hQ⟩ := exists_canonicalPoint B S hS 𝒳 g hx hx' κ hκ
  let c₀ := e.hom.functor.obj Q
  have hc₀ : c₀.base = Q.x := Functor.congr_obj e.hom.w Q
  let s₀ : F.obj (op (overObj B S hS g)) :=
    F.map (eqToHom (hc₀.trans hQx).symm).op c₀.fiber.as
  let c : (presheafOfCategories (F ⋙ typeToCat)).obj := ⟨overObj B S hS g, Discrete.mk s₀⟩
  let m : c ⟶ c₀ := ⟨eqToHom (hc₀.trans hQx).symm, Discrete.eqToHom' rfl⟩
  have hsec : sectionArrow B S hS 𝒳 U U' x hx yV F e c ≫ κ =
      cartArrow B S hS 𝒳 U' x' hx' ((Over.iteratedSliceBackward U').obj (overObj B S hS g)) := by
    rw [← sectionArrow_comp B S hS 𝒳 U U' x hx yV F e m,
      sectionArrow_hom_obj B S hS 𝒳 U U' x hx yV F e Q hc₀]
    rw [← hQ]
    simp only [Category.assoc, ← Functor.map_comp_assoc]
    change yV.map (eqToHom (hc₀.trans hQx).symm ≫ eqToHom hc₀) ≫ _ = yV.map (eqToHom _) ≫ _
    rw [eqToHom_trans]
  -- the field-valued point over `u₀`
  have hκc : B.Contains (Spec (.of (U.left.1.residueField u₀))) :=
    B.residueField_spec_contains U.left.2 u₀
  let toB : Spec (.of (U.left.1.residueField u₀)) ⟶ U'.left.1 :=
    U.left.1.fromSpecResidueField u₀ ≫ B.inclusion.map g.left
  let site₀ : AlgebraicGeometry.BigFppfOver B U'.left.1 U'.left.2 :=
    Over.mk (⟨toB⟩ : B.obj hκc ⟶ B.obj U'.left.2)
  let ρ : site₀ ⟶ overObj B S hS g :=
    Over.homMk ⟨U.left.1.fromSpecResidueField u₀⟩ (by apply ObjectProperty.hom_ext; rfl)
  let z₀ : AlgebraicGeometry.Space.FieldValuedPoint B U'.left.1 U'.left.2 F :=
    ⟨U.left.1.residueField u₀, hκc, toB, F.map ρ.op s₀⟩
  have hTop : AlgebraicGeometry.IsAlgebraicSpace B U'.left.1 U'.left.2
      (⊤_ ((AlgebraicGeometry.BigFppfOver B U'.left.1 U'.left.2)ᵒᵖ ⥤ Type u)) :=
    AlgebraicGeometry.Space.isAlgebraicSpace_of_iso B U'.left.1 U'.left.2
      ((Over.mkIdTerminal.isTerminalObj yoneda
        (Over.mk (𝟙 (B.obj U'.left.2)))).uniqueUpToIso terminalIsTerminal)
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B U'.left.1 U'.left.2
        (Over.mk (𝟙 (B.obj U'.left.2))))
  have hgl : LocallyOfFiniteType (B.inclusion.map g.left) := by
    have h : B.inclusion.map g.left ≫ B.inclusion.map U'.hom = B.inclusion.map U.hom := by
      rw [← Functor.map_comp, Over.w g]
    have : LocallyOfFiniteType (B.inclusion.map g.left ≫ B.inclusion.map U'.hom) := by
      rw [h]; infer_instance
    exact locallyOfFiniteType_of_comp (B.inclusion.map g.left) (B.inclusion.map U'.hom)
  have hz₀ : AlgebraicGeometry.Space.IsFiniteTypePoint B U'.left.1 U'.left.2 F
      (z₀.class B U'.left.1 U'.left.2 F) := by
    refine ⟨z₀, rfl, ?_⟩
    refine AlgebraicGeometry.Space.isLocallyOfFiniteType_of_comp B U'.left.1 U'.left.2
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B U'.left.1 U'.left.2 _) hF hTop _
      (terminal.from F) ?_
    have hk : AlgebraicGeometry.Space.IsLocallyOfFiniteType B U'.left.1 U'.left.2
        (yoneda.map (Over.homMk (⟨toB⟩ : B.obj hκc ⟶ B.obj U'.left.2) (by simp; rfl) :
          site₀ ⟶ Over.mk (𝟙 (B.obj U'.left.2)))) := by
      rw [AlgebraicGeometry.Space.isLocallyOfFiniteType_yoneda_map_iff]
      have := hu₀.1
      change LocallyOfFiniteType toB
      infer_instance
    exact AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_isTerminal B U'.left.1 U'.left.2
      (Over.mkIdTerminal.isTerminalObj yoneda _) terminalIsTerminal _ _ hk
  -- the point of `U` under the field-valued point is `u₀`
  let c₁ : (presheafOfCategories (F ⋙ typeToCat)).obj := ⟨site₀, Discrete.mk z₀.value⟩
  let m₁ : c₁ ⟶ c := ⟨ρ, Discrete.eqToHom' rfl⟩
  let η := baseChangeProjection B S hS 𝒳 U U' x hx yV F e
  have hsec₁ : sectionArrow B S hS 𝒳 U U' x hx yV F e c₁ ≫ κ =
      cartArrow B S hS 𝒳 U' x' hx' ((Over.iteratedSliceBackward U').obj site₀) := by
    rw [← sectionArrow_comp B S hS 𝒳 U U' x hx yV F e m₁, Category.assoc, hsec]
    exact map_cartArrow B S hS 𝒳 U' x' hx' ((Over.iteratedSliceBackward U').map ρ)
  have hηg : η.app c₁ ≫ g = ((Over.iteratedSliceBackward U').obj site₀).hom := by
    have h1 := sectionArrow_isHomLift B S hS 𝒳 U U' x hx yV F e hyV c₁
    have h2 : p.IsHomLift (η.app c₁ ≫ g) (sectionArrow B S hS 𝒳 U U' x hx yV F e c₁ ≫ κ) :=
      @IsHomLift.comp _ _ _ _ p _ _ _ _ _ _ _ _ _ _ h1 hκ
    rw [hsec₁] at h2
    have h3 := cartArrow_isHomLift B S hS 𝒳 U' x' hx' ((Over.iteratedSliceBackward U').obj site₀)
    exact (IsHomLift.fac p (η.app c₁ ≫ g) _).trans
      (@IsHomLift.fac _ _ _ _ p _ _ _ _ _ _ h3).symm
  have hpt : B.inclusion.map (η.app c₁).left (IsLocalRing.closedPoint _) = u₀ := by
    have h := congrArg (fun m => B.inclusion.map m.left) hηg
    simp only [Over.comp_left, Functor.map_comp] at h
    have h' : B.inclusion.map (η.app c₁).left = U.left.1.fromSpecResidueField u₀ :=
      (cancel_mono (B.inclusion.map g.left)).mp h
    rw [h']
    exact Scheme.fromSpecResidueField_apply _ _
  have hzu : let : Category (TwoFibreProductOver (Over.map U'.hom) (Over.forget U) p yV
        (Functor.TwoYoneda.liftBased p hp U ⟨x, hx⟩).toFunctor) :=
        TwoFibreProductOver.instCategory
      let P := e.inv.functor.obj ⟨z₀.siteObject, Discrete.mk z₀.value⟩
      ∃ hP : P.x = z₀.siteObject,
        (B.inclusion.map ((eqToHom (P.hx.trans P.hy.symm) ≫ P.y.hom).left))
          ((B.inclusion.map (eqToHom (congrArg Over.left hP).symm))
            (IsLocalRing.closedPoint z₀.carrier)) = u₀ := by
    have hP := inv_obj_x e c₁
    exact ⟨hP, (baseChangeProjection_point B S hS 𝒳 U U' x hx yV F e z₀ hP).symm.trans hpt⟩
  have hsm := isSmoothAt_baseChange_of_isVersalAt B S hS 𝒳 hΔ
    (AlgebraicGeometry.Stack.isLocallyOfFiniteType_isomSpace_of_isLimitPreserving B S hS 𝒳 hlim)
    (Deformation.Artin.satisfiesRS_of_satisfiesRSStar B S hS p hp hRS) U U' x hx u₀ hu₀ yV hyV
    F hF e z₀ hz₀ hzu hversal
  obtain ⟨Z₀, hZ₀, z₀', hz₀', hsmZ⟩ := hsm
  let p₀ : AlgebraicGeometry.Space.FieldValuedPoint B U'.left.1 U'.left.2
      (yoneda.obj (overObj B S hS g)) := ⟨U.left.1.residueField u₀, hκc, toB, ρ⟩
  obtain ⟨V, hV, hpV, hfac⟩ := AlgebraicGeometry.Space.exists_isOpen_factor_openSubspace B
    U'.left.1 U'.left.2 hF Z₀ hZ₀ (overObj B S hS g) (yonedaEquiv.symm s₀) p₀ ⟨z₀', hz₀'⟩
  have key : (U.left.1.fromSpecResidueField u₀) (IsLocalRing.closedPoint _) = u₀ :=
    Scheme.fromSpecResidueField_apply _ _
  have key' : AlgebraicGeometry.Space.schemePoint B U'.left.1 U'.left.2 (overObj B S hS g) p₀ =
      u₀ := key
  exact ⟨F, hF, e, s₀, Z₀, hZ₀, hsmZ, hsec, V, hV, key' ▸ hpV, hfac⟩

/-- `Deformation.Artin.BaseChange.exists_smooth_openSubspace_isOpen_of_isVersalAt`, read at a
generization `u` of `u₀`: the section `s₀` sends `u` into `Z₀`. -/
theorem exists_smooth_openSubspace_of_isVersalAt [IsLocallyNoetherian S]
    (hΔ : AlgebraicGeometry.Stack.HasRepresentableDiagonal B S hS 𝒳)
    (hRS : Deformation.Artin.SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids)
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, w, v} B S hS 𝒳)
    {U U' : AlgebraicGeometry.BigFppfOver B S hS} [LocallyOfFiniteType (B.inclusion.map U.hom)]
    [LocallyOfFiniteType (B.inclusion.map U'.hom)] (g : U ⟶ U')
    (hgmono : Mono (B.inclusion.map g.left))
    {x x' : 𝒳.val.obj} (hx : 𝒳.val.p.obj x = U) (hx' : 𝒳.val.p.obj x' = U')
    (κ : x ⟶ x') (hκ : 𝒳.val.p.IsHomLift g κ)
    (u₀ u : U.left.1) (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀) (hspec : u ⤳ u₀)
    (hversal : Deformation.Artin.IsVersalAt (Over.mk (B.inclusion.map U.hom))
      (𝒳.val.p ⋙ Over.post B.inclusion) u₀ x
      (by simpa using congrArg (Over.post B.inclusion).obj hx)) :
    ∃ (F : (AlgebraicGeometry.BigFppfOver B U'.left.1 U'.left.2)ᵒᵖ ⥤ Type u)
      (_ : AlgebraicGeometry.IsAlgebraicSpace B U'.left.1 U'.left.2 F)
      (e : BaseChangeEquivalence B S hS 𝒳 U U' x hx (twoYoneda B S hS 𝒳 U' x' hx') F)
      (s₀ : F.obj (op (overObj B S hS g))) (Z₀ : Subfunctor F),
      AlgebraicGeometry.Space.IsOpenSubspace B U'.left.1 U'.left.2 Z₀ ∧
      AlgebraicGeometry.Space.IsSmooth B U'.left.1 U'.left.2 (Z₀.ι ≫ terminal.from F) ∧
      sectionArrow B S hS 𝒳 U U' x hx (twoYoneda B S hS 𝒳 U' x' hx') F e
          ⟨overObj B S hS g, Discrete.mk s₀⟩ ≫ κ =
        cartArrow B S hS 𝒳 U' x' hx' ((Over.iteratedSliceBackward U').obj (overObj B S hS g)) ∧
      ∀ (Y : AlgebraicGeometry.BigFppfOver B U'.left.1 U'.left.2) (h : Y ⟶ overObj B S hS g),
        (∀ y, (AlgebraicGeometry.BigFppfOver.toScheme B U'.left.1 U'.left.2).map h y = u) →
        ∃ α : yoneda.obj Y ⟶ Z₀.toFunctor, α ≫ Z₀.ι = yoneda.map h ≫ yonedaEquiv.symm s₀ := by
  obtain ⟨F, hF, e, s₀, Z₀, hZ₀, hsmZ, hsec, V, hV, hu₀V, hfac⟩ :=
    exists_smooth_openSubspace_isOpen_of_isVersalAt B S hS 𝒳 hΔ hRS hlim g hgmono hx hx' κ hκ u₀
      hu₀ hversal
  exact ⟨F, hF, e, s₀, Z₀, hZ₀, hsmZ, hsec, fun Y h hh => hfac Y h fun y =>
    (hh y).symm ▸ hspec.mem_open hV hu₀V⟩

/-- **A lifting problem solved through a section of the representing space.** Let `κ : x ⟶ x'`
lie over a monomorphism `g`, and let `s₀` be the section over `U` whose arrow is `κ`. Given a
section `c''` of `F` over `B''` restricting along `i'' : A'' ⟶ B''` to the restriction of `s₀`,
the lifting problem `(i''_X : y'' ⟶ z'', py ≫ a : y'' ⟶ x)` has a solution, as soon as `y''` and
`z''` map to `x'` over the structure morphisms of `A''` and `B''`. -/
theorem exists_lift_of_section {U U' : AlgebraicGeometry.BigFppfOver B S hS} (g : U ⟶ U')
    (hgmono : Mono g)
    {x x' : 𝒳.val.obj} (hx : 𝒳.val.p.obj x = U) (hx' : 𝒳.val.p.obj x' = U')
    (κ : x ⟶ x') (hκ : 𝒳.val.p.IsHomLift g κ)
    (F : (AlgebraicGeometry.BigFppfOver B U'.left.1 U'.left.2)ᵒᵖ ⥤ Type u)
    (e : BaseChangeEquivalence B S hS 𝒳 U U' x hx (twoYoneda B S hS 𝒳 U' x' hx') F)
    (s₀ : F.obj (op (overObj B S hS g)))
    (hsec : sectionArrow B S hS 𝒳 U U' x hx (twoYoneda B S hS 𝒳 U' x' hx') F e
          ⟨overObj B S hS g, Discrete.mk s₀⟩ ≫ κ =
        cartArrow B S hS 𝒳 U' x' hx' ((Over.iteratedSliceBackward U').obj (overObj B S hS g)))
    {AV A''V B''V : AlgebraicGeometry.BigFppfOver B U'.left.1 U'.left.2}
    (hAV : AV ⟶ overObj B S hS g) (pA : A''V ⟶ AV) (i'' : A''V ⟶ B''V)
    (c'' : F.obj (op B''V)) (hc'' : F.map i''.op c'' = F.map (pA ≫ hAV).op s₀)
    {y z y'' z'' : 𝒳.val.obj} (hy'' : 𝒳.val.p.obj y'' = (Over.map U'.hom).obj A''V)
    (hz'' : 𝒳.val.p.obj z'' = (Over.map U'.hom).obj B''V)
    (a : y ⟶ x) (i : y ⟶ z) (ζ : z ⟶ x') (hcompat : a ≫ κ = i ≫ ζ)
    (py : y'' ⟶ y) (pz : z'' ⟶ z) (i''X : y'' ⟶ z'') (hcomm : i''X ≫ pz = py ≫ i)
    (hpzζ : 𝒳.val.p.IsHomLift ((Over.iteratedSliceBackward U').obj B''V).hom (pz ≫ ζ))
    (hpya : 𝒳.val.p.IsHomLift ((Over.iteratedSliceBackward U').obj A''V).hom (py ≫ a ≫ κ))
    (hi''X : 𝒳.val.p.IsHomLift ((Over.map U'.hom).map i'') i''X) :
    ∃ b'' : z'' ⟶ x, i''X ≫ b'' = py ≫ a := by
  classical
  let p := 𝒳.val.p
  have hp := 𝒳.isFiberedInGroupoids
  let yV := twoYoneda B S hS 𝒳 U' x' hx'
  have hyV : yV ⋙ p = Over.map U'.hom := twoYoneda_comp B S hS 𝒳 U' x' hx'
  let cartA := cartArrow B S hS 𝒳 U' x' hx' ((Over.iteratedSliceBackward U').obj A''V)
  let cartB := cartArrow B S hS 𝒳 U' x' hx' ((Over.iteratedSliceBackward U').obj B''V)
  have hcA := cartArrow_isHomLift B S hS 𝒳 U' x' hx' ((Over.iteratedSliceBackward U').obj A''V)
  have hcB := cartArrow_isHomLift B S hS 𝒳 U' x' hx' ((Over.iteratedSliceBackward U').obj B''V)
  have hcBs : p.IsStronglyCartesian ((Over.iteratedSliceBackward U').obj B''V).hom cartB :=
    hp.isStronglyCartesian_homLift _ cartB
  obtain ⟨σA, hσA, hσAf⟩ := @exists_vertical_iso _ _ _ _ p hp _ _ _ _ _ _ hy''
    (Functor.congr_obj hyV A''V) (py ≫ a ≫ κ) cartA hpya hcA
  obtain ⟨σB, hσB, hσBf⟩ := @exists_vertical_iso _ _ _ _ p hp _ _ _ _ _ _ hz''
    (Functor.congr_obj hyV B''V) (pz ≫ ζ) cartB hpzζ hcB
  let cB : (presheafOfCategories (F ⋙ typeToCat)).obj := ⟨B''V, Discrete.mk c''⟩
  let cA : (presheafOfCategories (F ⋙ typeToCat)).obj := ⟨A''V, Discrete.mk (F.map i''.op c'')⟩
  let c₀ : (presheafOfCategories (F ⋙ typeToCat)).obj := ⟨overObj B S hS g, Discrete.mk s₀⟩
  let mAB : cA ⟶ cB := ⟨i'', Discrete.eqToHom' rfl⟩
  let mA0 : cA ⟶ c₀ := ⟨pA ≫ hAV, Discrete.eqToHom' hc''⟩
  refine ⟨σB.hom ≫ sectionArrow B S hS 𝒳 U U' x hx yV F e cB, ?_⟩
  have hstep : i''X ≫ σB.hom = σA.hom ≫ yV.map i'' := by
    have h1 : p.IsHomLift ((Over.map U'.hom).map i'') (i''X ≫ σB.hom) := by
      simpa using @IsHomLift.comp _ _ _ _ p _ _ _ _ _ _ _ _ _ _ hi''X hσB
    have hyVi : p.IsHomLift ((Over.map U'.hom).map i'') (yV.map i'') := by
      refine IsHomLift.of_fac' p _ _ (Functor.congr_obj hyV A''V) (Functor.congr_obj hyV B''V) ?_
      exact Functor.congr_hom hyV i''
    have h2 : p.IsHomLift ((Over.map U'.hom).map i'') (σA.hom ≫ yV.map i'') := by
      simpa using @IsHomLift.comp _ _ _ _ p _ _ _ _ _ _ _ _ _ _ hσA hyVi
    refine @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _ _ cartB hcBs _ _ _ (i''X ≫ σB.hom)
      (σA.hom ≫ yV.map i'') h1 h2 ?_
    rw [Category.assoc, hσBf, Category.assoc,
      show yV.map i'' ≫ cartB = cartA from map_cartArrow B S hS 𝒳 U' x' hx'
        ((Over.iteratedSliceBackward U').map i''), hσAf, ← Category.assoc, hcomm,
      Category.assoc, ← hcompat]
  have hval : i''X ≫ σB.hom ≫ sectionArrow B S hS 𝒳 U U' x hx yV F e cB =
      σA.hom ≫ yV.map (pA ≫ hAV) ≫ sectionArrow B S hS 𝒳 U U' x hx yV F e c₀ := by
    rw [← Category.assoc, hstep, Category.assoc,
      sectionArrow_comp B S hS 𝒳 U U' x hx yV F e mAB,
      ← sectionArrow_comp B S hS 𝒳 U U' x hx yV F e mA0]
  -- both arrows `y'' ⟶ x` agree after `κ`, which lies over a monomorphism
  have hκcomp : (i''X ≫ σB.hom ≫ sectionArrow B S hS 𝒳 U U' x hx yV F e cB) ≫ κ =
      (py ≫ a) ≫ κ := by
    rw [hval, Category.assoc, Category.assoc, hsec,
      show yV.map (pA ≫ hAV) ≫ cartArrow B S hS 𝒳 U' x' hx'
          ((Over.iteratedSliceBackward U').obj (overObj B S hS g)) = cartA from
        map_cartArrow B S hS 𝒳 U' x' hx' ((Over.iteratedSliceBackward U').map (pA ≫ hAV)),
      hσAf, Category.assoc]
  have hmono : Mono (p.map κ) := by
    rw [IsHomLift.fac' p g κ]
    infer_instance
  have hpm : p.map (i''X ≫ σB.hom ≫ sectionArrow B S hS 𝒳 U U' x hx yV F e cB) =
      p.map (py ≫ a) := by
    rw [← cancel_mono (p.map κ), ← Functor.map_comp, ← Functor.map_comp, hκcomp]
  have hκs : p.IsStronglyCartesian (p.map κ) κ := hp.isStronglyCartesian_homLift _ κ
  have hl1 : p.IsHomLift (p.map (py ≫ a))
      (i''X ≫ σB.hom ≫ sectionArrow B S hS 𝒳 U U' x hx yV F e cB) := by
    rw [← hpm]; infer_instance
  exact Functor.IsStronglyCartesian.ext p (p.map κ) κ (p.map (py ≫ a)) hκcomp

end Deformation.Artin.BaseChange
