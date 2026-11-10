module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionVersality
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FunctorForm
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# Versality of an element of Artin's contraction functor away from `Z`

In the situation of Stacks 0GH8 let `F` be Artin's contraction functor of Stacks 0GHA and let
`ξ = (Z, u', x̂) ∈ F(V)`. Write `V° ⊆ V` for the open subscheme with underlying set `|V| ∖ Z` and
`s° ∈ X'(V°)` for the point of `X'` given by `u' : V ∖ Z ⟶ U' ⊆ X'`. This file shows that at a
point of `V°` the element `ξ` is versal exactly when `s°` is versal as an object of the category
fibred in groupoids attached to the algebraic space `X'` (Stacks 0458): a lifting problem for `ξ`
whose closed point lands outside `Z` lives entirely in `V°`, where triples are points of `U'`.

## Main definitions

* `AlgebraicGeometry.Artin.ContractionSituation.Triple.openPart`: the open subset `|V| ∖ Z` of
  the scheme `V`.
* `AlgebraicGeometry.Artin.ContractionSituation.Triple.openObj`: the open subscheme `V°`, as an
  object of the site.
* `AlgebraicGeometry.Artin.ContractionSituation.Triple.openPoint`: the point `s° ∈ X'(V°)`.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.isVersalAt_iff_isVersalAt_openPoint`: versality
  of `ξ` at a point of `V°` is versality of `s°` there.

## References

* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 07XF](https://stacks.math.columbia.edu/tag/07XF)
* [Stacks Project, Tag 0GHA](https://stacks.math.columbia.edu/tag/0GHA)
* [Stacks Project, Tag 0GIA](https://stacks.math.columbia.edu/tag/0GIA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of the site whose image lies in the image of a morphism `ι` whose underlying
morphism of schemes is an open immersion factors through `ι`. -/
private theorem exists_comp_eq_of_isOpenImmersion_aux {T V V₀ : BigFppfOver B S hS} (ι : V₀ ⟶ V)
    (hι : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ι))
    (φ : T ⟶ V) (h : Set.range ((BigFppfOver.toScheme B S hS).map φ) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map ι)) :
    ∃ φ' : T ⟶ V₀, φ' ≫ ι = φ := by
  let l := IsOpenImmersion.lift ((BigFppfOver.toScheme B S hS).map ι)
    ((BigFppfOver.toScheme B S hS).map φ) h
  have hl : l ≫ (BigFppfOver.toScheme B S hS).map ι = (BigFppfOver.toScheme B S hS).map φ :=
    IsOpenImmersion.lift_fac _ _ _
  refine ⟨Over.homMk (ObjectProperty.homMk (X := T.left) (Y := V₀.left) l) ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    rw [ObjectProperty.FullSubcategory.comp_hom]
    have hV₀ : V₀.hom.hom = ι.left.hom ≫ V.hom.hom :=
      (congrArg (fun m => m.hom) (Over.w ι)).symm
    change l ≫ V₀.hom.hom = T.hom.hom
    have hl' : l ≫ ι.left.hom = φ.left.hom := hl
    rw [hV₀, ← Category.assoc, hl']
    exact congrArg (fun m => m.hom) (Over.w φ)
  · apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact hl

/-- A morphism of the site whose image lies in an open `O` of the target factors through the
open subscheme `O`, read as an object of the site. -/
theorem exists_comp_openSubHom_eq {T V : BigFppfOver B S hS} (O : V.left.obj.Opens) (φ : T ⟶ V)
    (h : Set.range ((BigFppfOver.toScheme B S hS).map φ) ⊆ (O : Set V.left.obj)) :
    ∃ φ' : T ⟶ openSubObj B S hS V O, φ' ≫ openSubHom B S hS V O = φ :=
  exists_comp_eq_of_isOpenImmersion_aux (openSubHom B S hS V O)
    (inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion O.ι)) φ
    (h.trans (Scheme.Opens.range_ι O).ge)

/-- A morphism of the site whose image lies in the image of a morphism `ι` whose underlying
morphism of schemes is an open immersion factors through `ι`. -/
theorem exists_comp_eq_of_isOpenImmersion {T V V₀ : BigFppfOver B S hS} (ι : V₀ ⟶ V)
    (hι : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ι))
    (φ : T ⟶ V) (h : Set.range ((BigFppfOver.toScheme B S hS).map φ) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map ι)) :
    ∃ φ' : T ⟶ V₀, φ' ≫ ι = φ :=
  exists_comp_eq_of_isOpenImmersion_aux ι hι φ h

/-- Two morphisms into an open subscheme, read as an object of the site, agree as soon as they
agree after the inclusion. -/
theorem eq_of_comp_openSubHom_eq {T V : BigFppfOver B S hS} (O : V.left.obj.Opens)
    {φ ψ : T ⟶ openSubObj B S hS V O}
    (h : φ ≫ openSubHom B S hS V O = ψ ≫ openSubHom B S hS V O) : φ = ψ := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  have h' := congrArg (fun m => m.left.hom) h
  exact (cancel_mono O.ι).1 h'

end BigFppfOver

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A section of a presheaf over a one-point object of the site lies in the open subspace cut out
by `W` as soon as its restriction to a nonempty object does. -/
theorem mem_openSubspaceOfPoints_of_map {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T T' : BigFppfOver B S hS} [Subsingleton ((BigFppfOver.toScheme B S hS).obj T')]
    (t : (BigFppfOver.toScheme B S hS).obj T) (ι : T ⟶ T') (s : P.obj (op T'))
    (W : Set (points B S hS P))
    (h : P.map ι.op s ∈ (openSubspaceOfPoints B S hS P W).obj (op T)) :
    s ∈ (openSubspaceOfPoints B S hS P W).obj (op T') := by
  rw [mem_openSubspaceOfPoints_iff] at h ⊢
  rintro _ ⟨w', rfl⟩
  have hw : w' = pointsMap B S hS (yoneda.obj T) (yoneda.map ι)
      ((pointsEquivScheme B S hS T).symm t) := by
    apply (pointsEquivScheme B S hS T').injective
    exact Subsingleton.elim _ _
  rw [hw, ← pointsMap_comp_apply]
  refine h ⟨(pointsEquivScheme B S hS T).symm t, ?_⟩
  congr 1
  rw [yonedaEquiv_symm_map]
  rfl

end Space

namespace Artin.ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS)

/-- A morphism `φ : T ⟶ V` avoids the closed subset of a triple exactly when the transported
triple has empty closed subset. -/
theorem mapTriple_Z_eq_empty_iff {T V : BigFppfOver B S hS} (φ : T ⟶ V) (t : Triple c V) :
    (mapTriple c φ t).Z = ∅ ↔
      φ ∈ (Space.openSubspaceOfPoints B S hS (yoneda.obj V) t.Zᶜ).obj (op T) := by
  have hy : yonedaEquiv.symm φ = yoneda.map φ := by ext; rfl
  rw [Space.mem_openSubspaceOfPoints_iff, hy, mapTriple_Z_eq_preimage,
    Set.eq_empty_iff_forall_notMem]
  constructor
  · rintro h _ ⟨w, rfl⟩ hw
    exact h w hw
  · intro h w hw
    exact h ⟨w, rfl⟩ hw

/-! ### The open part of a triple -/

attribute [local instance] Space.pointTopology

variable {c} in
/-- The open subset `|V| ∖ Z` of the scheme `V` of a triple `(Z, u', x̂)` over `V`. -/
def Triple.openPart {V : BigFppfOver B S hS} (t : Triple c V) : V.left.obj.Opens :=
  ⟨Space.pointsToScheme B S hS V '' t.Zᶜ,
    (Space.isOpen_pointTopology_yoneda_iff_isOpen_image B S hS V _).1
      t.isClosed_Z.isOpen_compl⟩

variable {c} in
/-- The open subscheme `V° ⊆ V` with underlying set `|V| ∖ Z`, as an object of the site. -/
abbrev Triple.openObj {V : BigFppfOver B S hS} (t : Triple c V) : BigFppfOver B S hS :=
  BigFppfOver.openSubObj B S hS V t.openPart

variable {c} in
/-- The inclusion `V° ⟶ V`. -/
abbrev Triple.openHom {V : BigFppfOver B S hS} (t : Triple c V) : t.openObj ⟶ V :=
  BigFppfOver.openSubHom B S hS V t.openPart

variable {c} in
/-- A morphism `φ : T ⟶ V` whose image lies in `V°` avoids `Z`. -/
theorem Triple.mem_openSubspaceOfPoints_of_range {T V : BigFppfOver B S hS} (t : Triple c V)
    (φ : T ⟶ V)
    (h : Set.range ((BigFppfOver.toScheme B S hS).map φ) ⊆ (t.openPart : Set V.left.obj)) :
    φ ∈ (Space.openSubspaceOfPoints B S hS (yoneda.obj V) t.Zᶜ).obj (op T) := by
  have hy : yonedaEquiv.symm φ = yoneda.map φ := by ext; rfl
  rw [Space.mem_openSubspaceOfPoints_iff, hy]
  rintro _ ⟨w, rfl⟩
  have hw := h ⟨Space.pointsToScheme B S hS T w, rfl⟩
  rw [← Space.pointsToScheme_pointsMap_yoneda] at hw
  obtain ⟨w', hw', he⟩ := hw
  rw [← (Space.injective_pointsToScheme B S hS V) he]
  exact hw'

variable {c} in
/-- The inclusion `V° ⟶ V` avoids `Z`. -/
theorem Triple.openHom_mem {V : BigFppfOver B S hS} (t : Triple c V) :
    t.openHom ∈ (Space.openSubspaceOfPoints B S hS (yoneda.obj V) t.Zᶜ).obj (op t.openObj) := by
  refine t.mem_openSubspaceOfPoints_of_range _ ?_
  rintro _ ⟨w, rfl⟩
  have hr := Scheme.Opens.range_ι t.openPart
  rw [← hr]
  exact ⟨w, rfl⟩

variable {c} in
/-- The point `s° ∈ X'(V°)` of `X'` given by `u' : V ∖ Z ⟶ U' ⊆ X'`. -/
def Triple.openPoint {V : BigFppfOver B S hS} (t : Triple c V) : c.X'.obj (op t.openObj) :=
  (t.u.app (op t.openObj) ⟨t.openHom, t.openHom_mem⟩).1

variable {c} in
/-- `u'` applied to `φ ≫ (V° ⟶ V)` is the restriction of `s°` along `φ`. -/
theorem Triple.u_app_comp_openHom {T V : BigFppfOver B S hS} (t : Triple c V)
    (φ : T ⟶ t.openObj) (h) :
    (t.u.app (op T) ⟨φ ≫ t.openHom, h⟩).1 = c.X'.map φ.op t.openPoint := by
  have e : (⟨φ ≫ t.openHom, h⟩ :
      (Space.openSubspaceOfPoints B S hS (yoneda.obj V) t.Zᶜ).toFunctor.obj (op T)) =
      (Space.openSubspaceOfPoints B S hS (yoneda.obj V) t.Zᶜ).toFunctor.map φ.op
        ⟨t.openHom, t.openHom_mem⟩ := rfl
  rw [e]
  exact congrArg Subtype.val (NatTrans.naturality_apply t.u φ.op _)

variable {c} in
/-- The object `s°` of the category fibred in groupoids attached to `X'`, over `V°`. -/
abbrev Triple.openObject {V : BigFppfOver B S hS} (t : Triple c V) :
    (Stack.fibredCategory B S hS c.X').val.obj :=
  ⟨t.openObj, Discrete.mk t.openPoint⟩

/-- A morphism into `V°` followed by the inclusion `V° ⟶ V` avoids `Z`. -/
private theorem comp_openHom_mem {T V : BigFppfOver B S hS} (t : Triple c V) (φ₀ : T ⟶ t.openObj) :
    φ₀ ≫ t.openHom ∈ (Space.openSubspaceOfPoints B S hS (yoneda.obj V) t.Zᶜ).obj (op T) :=
  ((Space.openSubspaceOfPoints B S hS (yoneda.obj V) t.Zᶜ).toFunctor.map φ₀.op
    ⟨t.openHom, t.openHom_mem⟩).2

/-- The point of `U'` of the transported triple of a morphism factoring through `V°` is the
restriction of `s°`. -/
private theorem uPoint_mapTriple_eq_map_openPoint {T V : BigFppfOver B S hS} (t : Triple c V)
    (φ₀ : T ⟶ t.openObj) (φ : T ⟶ V) (hφ : φ₀ ≫ t.openHom = φ) (h : (mapTriple c φ t).Z = ∅) :
    ((mapTriple c φ t).uPoint h).1 = c.X'.map φ₀.op t.openPoint := by
  subst hφ
  rw [uPoint_mapTriple_eq c _ t (comp_openHom_mem c t φ₀) h]
  exact t.u_app_comp_openHom φ₀ _

/-- A morphism `φ` of the site out of a one-point object sends its point to `g y` when `ρ`
followed by `φ` is `g`. -/
theorem exists_map_eq_of_comp_eq {T V : BigFppfOver B S hS} {X Y : Scheme.{u}}
    (e : X = (BigFppfOver.toScheme B S hS).obj T) (ρ : Y ⟶ X) (φ : T ⟶ V)
    (g : Y ⟶ (BigFppfOver.toScheme B S hS).obj V)
    (h : ρ ≫ eqToHom e ≫ ((Over.post B.inclusion).map φ).left = g) (y : Y) :
    ∃ t, (BigFppfOver.toScheme B S hS).map φ t = g y :=
  ⟨(ρ ≫ eqToHom e) y, by rw [← h]; rfl⟩

/-- **The lifting problems for `ξ` at a point of `V°` are those for `s°`.** Over a chart
`Spec Λ ⟶ S`, the lifting property of `s°` at a residue point `κ` of `V°` is the lifting
property of `ξ` at `κ` followed by the inclusion `V° ⟶ V`. -/
theorem liftsAtResiduePoint_openObject_iff {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ S) (x : (contractionFunctor c).Elementsᵒᵖ)
    (κ : Spec (.of k) ⟶
      ((Over.post B.inclusion).obj (x.unop.2 : Triple c x.unop.1.unop.obj).openObj).left) :
    Deformation.Artin.LiftsAtResiduePoint iΛ
        ((Stack.fibredCategory B S hS c.X').val.p ⋙ Over.post B.inclusion)
        (((Stack.fibredCategory B S hS c.X').val.p ⋙ Over.post B.inclusion).obj
          (x.unop.2 : Triple c x.unop.1.unop.obj).openObject)
        (x.unop.2 : Triple c x.unop.1.unop.obj).openObject rfl κ ↔
      Deformation.Artin.LiftsAtResiduePoint iΛ
        (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c))
        ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj x) x rfl
        (κ ≫ ((Over.post B.inclusion).map
          (x.unop.2 : Triple c x.unop.1.unop.obj).openHom).left) := by
  let t : Triple c x.unop.1.unop.obj := x.unop.2
  let j := ((Over.post B.inclusion).map t.openHom).left
  have : Mono j := inferInstanceAs (Mono t.openPart.ι)
  have hjrange : ∀ w, j w ∈ (t.openPart : Set x.unop.1.unop.obj.left.obj) := by
    intro w
    have hr := Scheme.Opens.range_ι t.openPart
    rw [← hr]
    exact ⟨w, rfl⟩
  constructor
  · intro hU A A' f hf y z hy hz i hi a ha
    have : Subsingleton ((BigFppfOver.toScheme B S hS).obj y.unop.1.unop.obj) :=
      subsingleton_of_over_spec hy
    have : Subsingleton ((BigFppfOver.toScheme B S hS).obj z.unop.1.unop.obj) :=
      subsingleton_of_over_spec hz
    let ι := i.unop.1.unop.hom
    let φ := a.unop.1.unop.hom
    have ha' := ha
    simp only [Deformation.Artin.schemeMap, eqToHom_refl, Category.comp_id] at ha'
    obtain ⟨t₀, ht₀⟩ := exists_map_eq_of_comp_eq (T := y.unop.1.unop.obj)
      (V := x.unop.1.unop.obj) (congrArg Over.left hy).symm _ φ _ ha'
      (IsLocalRing.closedPoint k)
    have hrange : Set.range ((BigFppfOver.toScheme B S hS).map φ) ⊆
        (t.openPart : Set x.unop.1.unop.obj.left.obj) := by
      rintro _ ⟨t₁, rfl⟩
      rw [Subsingleton.elim t₁ t₀, ht₀]
      exact hjrange _
    have hmem := t.mem_openSubspaceOfPoints_of_range φ hrange
    obtain ⟨φ₀, hφ₀⟩ := BigFppfOver.exists_comp_openSubHom_eq t.openPart φ hrange
    have hya : mapTriple c φ t = y.unop.2 := a.unop.2
    have hzi : mapTriple c ι z.unop.2 = y.unop.2 := i.unop.2
    have hyZ : (y.unop.2 : Triple c y.unop.1.unop.obj).Z = ∅ := by
      rw [← hya]; exact (mapTriple_Z_eq_empty_iff c φ t).2 hmem
    have hzZ : (z.unop.2 : Triple c z.unop.1.unop.obj).Z = ∅ := by
      rcases Triple.Z_eq_empty_or_eq_univ (z.unop.2 : Triple c z.unop.1.unop.obj) with h | h
      · exact h
      · exfalso
        have h0 := Triple.mapTriple_Z_eq_univ c ι _ h
        rw [hzi, hyZ] at h0
        exact (Set.mem_empty_iff_false ((Space.pointsEquivScheme B S hS _).symm t₀)).1
          (h0 ▸ Set.mem_univ _)
    let sz := (z.unop.2 : Triple c z.unop.1.unop.obj).uPoint hzZ
    have hfib : c.X'.map φ₀.op t.openPoint = c.X'.map ι.op sz.1 := by
      rw [← uPoint_mapTriple_eq_map_openPoint c t φ₀ φ hφ₀
          ((mapTriple_Z_eq_empty_iff c φ t).2 hmem),
        Triple.uPoint_congr hya _ hyZ, ← Triple.uPoint_congr hzi
          (Triple.mapTriple_Z_eq_empty c ι _ hzZ) hyZ,
        Triple.uPoint_mapTriple ι _ hzZ]
      rfl
    let y𝒳 : (Stack.fibredCategory B S hS c.X').val.obj :=
      ⟨y.unop.1.unop.obj, Discrete.mk (c.X'.map φ₀.op t.openPoint)⟩
    let z𝒳 : (Stack.fibredCategory B S hS c.X').val.obj := ⟨z.unop.1.unop.obj, Discrete.mk sz.1⟩
    let i𝒳 : y𝒳 ⟶ z𝒳 := { base := ι, fiber := Discrete.eqToHom hfib }
    let a𝒳 : y𝒳 ⟶ t.openObject := { base := φ₀, fiber := Discrete.eqToHom rfl }
    have hy𝒳 : ((Stack.fibredCategory B S hS c.X').val.p ⋙ Over.post B.inclusion).obj y𝒳 =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) := hy
    have hz𝒳 : ((Stack.fibredCategory B S hS c.X').val.p ⋙ Over.post B.inclusion).obj z𝒳 =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ iΛ) := hz
    have ha𝒳 : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫
        Deformation.Artin.schemeMap
          ((Stack.fibredCategory B S hS c.X').val.p ⋙ Over.post B.inclusion) hy𝒳 rfl a𝒳 = κ := by
      have key : (Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫
          Deformation.Artin.schemeMap
            ((Stack.fibredCategory B S hS c.X').val.p ⋙ Over.post B.inclusion) hy𝒳 rfl a𝒳 :
            Spec (.of k) ⟶ ((Over.post B.inclusion).obj t.openObj).left) ≫ j = κ ≫ j := by
        refine Eq.trans ?_ ha'
        simp only [Deformation.Artin.schemeMap, Category.assoc]
        congr 2
        change ((Over.post B.inclusion).map φ₀ ≫ (Over.post B.inclusion).map t.openHom).left =
          ((Over.post B.inclusion).map φ).left
        rw [← Functor.map_comp, hφ₀]
      exact (cancel_mono j).1 key
    obtain ⟨b𝒳, hb𝒳⟩ := hU A A' f hf y𝒳 z𝒳 hy𝒳 hz𝒳 i𝒳 hi a𝒳 ha𝒳
    have hbfib : sz.1 = c.X'.map b𝒳.base.op t.openPoint :=
      Deformation.Artin.fiber_as_eq_of_hom b𝒳
    have hbase : ι ≫ b𝒳.base = φ₀ := congrArg (fun m => m.base) hb𝒳
    let φ' := b𝒳.base ≫ t.openHom
    have hZ' := (mapTriple_Z_eq_empty_iff c φ' t).2 (comp_openHom_mem c t b𝒳.base)
    have hb : mapTriple c φ' t = z.unop.2 := by
      refine Triple.ext_of_Z_eq_empty hZ' hzZ ?_
      change ((mapTriple c φ' t).uPoint hZ').1 = sz.1
      rw [uPoint_mapTriple_eq_map_openPoint c t b𝒳.base φ' rfl hZ', hbfib]
    refine ⟨Quiver.Hom.op ⟨(ObjectProperty.homMk φ' : z.unop.1.unop ⟶ x.unop.1.unop).op, hb⟩,
      ?_⟩
    apply Quiver.Hom.unop_inj
    apply Functor.Elements.hom_ext
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    change ι ≫ b𝒳.base ≫ t.openHom = φ
    rw [← Category.assoc, hbase, hφ₀]
  · intro hU A A' f hf y z hy hz i hi a ha
    obtain ⟨T, ⟨sy⟩⟩ := y
    obtain ⟨T', ⟨sz⟩⟩ := z
    have : Subsingleton ((BigFppfOver.toScheme B S hS).obj T) := subsingleton_of_over_spec hy
    have : Subsingleton ((BigFppfOver.toScheme B S hS).obj T') := subsingleton_of_over_spec hz
    let ι : T ⟶ T' := i.base
    let φ₀ : T ⟶ t.openObj := a.base
    have hiy : sy = c.X'.map ι.op sz := Deformation.Artin.fiber_as_eq_of_hom i
    have hay : sy = c.X'.map φ₀.op t.openPoint := Deformation.Artin.fiber_as_eq_of_hom a
    let φ := φ₀ ≫ t.openHom
    have hmem := comp_openHom_mem c t φ₀
    let t₀ : (BigFppfOver.toScheme B S hS).obj T :=
      (eqToHom (congrArg Over.left hy).symm) (IsLocalRing.closedPoint A)
    have hszmem : sz ∈ c.U'.obj (op T') := by
      refine Space.mem_openSubspaceOfPoints_of_map t₀ ι sz c.T'ᶜ ?_
      rw [← hiy, hay]
      exact (c.U'.toFunctor.map φ₀.op
        (t.u.app (op t.openObj) ⟨t.openHom, t.openHom_mem⟩)).2
    let u : yoneda.obj T' ⟶ c.U'.toFunctor := yonedaEquiv.symm ⟨sz, hszmem⟩
    have hu' : yonedaEquiv u = (⟨sz, hszmem⟩ : c.U'.toFunctor.obj (op T')) :=
      yonedaEquiv.apply_symm_apply _
    have hu : (yonedaEquiv u : c.U'.toFunctor.obj (op T')).1 = sz := by rw [hu']
    let TN : LocallyNoetherianOver B S hS := ⟨T, isLocallyNoetherian_of_over_spec hy⟩
    let T'N : LocallyNoetherianOver B S hS := ⟨T', isLocallyNoetherian_of_over_spec hz⟩
    let yF : (contractionFunctor c).Elementsᵒᵖ :=
      op ((contractionFunctor c).elementsMk (op TN) (mapTriple c φ t))
    let zF : (contractionFunctor c).Elementsᵒᵖ :=
      op ((contractionFunctor c).elementsMk (op T'N) (c.emptyTriple T' u))
    have hyZ : (mapTriple c φ t).Z = ∅ := (mapTriple_Z_eq_empty_iff c φ t).2 hmem
    have hiF : mapTriple c ι (c.emptyTriple T' u) = mapTriple c φ t := by
      refine Triple.ext_of_Z_eq_empty
        (Triple.mapTriple_Z_eq_empty c ι _ (c.emptyTriple_Z T' u)) hyZ ?_
      rw [Triple.uValue_mapTriple ι _ (c.emptyTriple_Z T' u)]
      change c.X'.map ι.op ((c.emptyTriple T' u).uPoint (c.emptyTriple_Z T' u)).1 =
        ((mapTriple c φ t).uPoint hyZ).1
      rw [uPoint_emptyTriple, hu, uPoint_mapTriple_eq_map_openPoint c t φ₀ φ rfl hyZ,
        ← hiy, hay]
    let iF : yF ⟶ zF := Quiver.Hom.op ⟨(ObjectProperty.homMk ι : TN ⟶ T'N).op, hiF⟩
    let aF : yF ⟶ x :=
      Quiver.Hom.op ⟨(ObjectProperty.homMk φ : TN ⟶ x.unop.1.unop).op, rfl⟩
    have hyF : (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj yF =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) := hy
    have hzF : (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj zF =
        Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ iΛ) := hz
    have haF : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫
        Deformation.Artin.schemeMap
          (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)) hyF rfl aF =
        κ ≫ j := by
      rw [← ha]
      simp only [Deformation.Artin.schemeMap, eqToHom_refl, Category.comp_id]
      rfl
    obtain ⟨b, hb⟩ := hU A A' f hf yF zF hyF hzF iF hi aF haF
    let φ' := b.unop.1.unop.hom
    have hb' : mapTriple c φ' t = c.emptyTriple T' u := b.unop.2
    have hZ' : (mapTriple c φ' t).Z = ∅ := by rw [hb']; exact c.emptyTriple_Z T' u
    have hmem' := (mapTriple_Z_eq_empty_iff c φ' t).1 hZ'
    have hrange : Set.range ((BigFppfOver.toScheme B S hS).map φ') ⊆
        (t.openPart : Set x.unop.1.unop.obj.left.obj) := by
      rintro _ ⟨t₁, rfl⟩
      have h₁ := (Space.mem_openSubspaceOfPoints_iff_of_subsingleton φ' t₁ _).1 hmem'
      refine ⟨_, h₁, ?_⟩
      exact (Space.pointsEquivScheme B S hS _).apply_symm_apply _
    obtain ⟨φ'₀, hφ'₀⟩ := BigFppfOver.exists_comp_openSubHom_eq t.openPart φ' hrange
    have hfib : sz = c.X'.map φ'₀.op t.openPoint := by
      rw [← uPoint_mapTriple_eq_map_openPoint c t φ'₀ φ' hφ'₀ hZ']
      have h₂ : ((mapTriple c φ' t).uPoint hZ').1 = sz := by
        rw [Triple.uPoint_congr hb' hZ' (c.emptyTriple_Z T' u), uPoint_emptyTriple]
        exact hu
      exact h₂.symm
    refine ⟨{ base := φ'₀, fiber := Discrete.eqToHom hfib }, ?_⟩
    apply Deformation.Artin.fibredCategory_hom_ext
    change ι ≫ φ'₀ = φ₀
    apply BigFppfOver.eq_of_comp_openSubHom_eq t.openPart
    rw [Category.assoc, hφ'₀]
    exact congrArg (fun m : yF ⟶ x => m.unop.1.unop.hom) hb

/-- **Versality of `ξ` at a point of `V°` is versality of `s°` there.** For
`ξ = (Z, u', x̂) ∈ F(V)` and a point `u` of the open subscheme `V° ⊆ V` with underlying set
`|V| ∖ Z`, the object `s° ∈ X'(V°)` of the category fibred in groupoids attached to `X'` is versal
at `u` exactly when `ξ` is versal at the image of `u` in `V`.

Both sides are read as the lifting property over an affine chart `Spec Λ ⊆ S` containing the
image of the residue point, where they agree by
`AlgebraicGeometry.Artin.ContractionSituation.liftsAtResiduePoint_openObject_iff`; the two residue
fields are identified by the open immersion `V° ⟶ V`, exactly as in
`Deformation.Artin.isVersalAt_iff_restrict`. -/
theorem isVersalAt_openObject_iff (x : (contractionFunctor c).Elementsᵒᵖ)
    (u : ((Over.post B.inclusion).obj (x.unop.2 : Triple c x.unop.1.unop.obj).openObj).left) :
    Deformation.Artin.IsVersalAt
        (((Stack.fibredCategory B S hS c.X').val.p ⋙ Over.post B.inclusion).obj
          (x.unop.2 : Triple c x.unop.1.unop.obj).openObject)
        ((Stack.fibredCategory B S hS c.X').val.p ⋙ Over.post B.inclusion) u
        (x.unop.2 : Triple c x.unop.1.unop.obj).openObject rfl ↔
      Deformation.Artin.IsVersalAt
        ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj x)
        (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c))
        (((Over.post B.inclusion).map (x.unop.2 : Triple c x.unop.1.unop.obj).openHom).left u)
        x rfl := by
  let t : Triple c x.unop.1.unop.obj := x.unop.2
  let q𝒳 : (Stack.fibredCategory B S hS c.X').val.obj ⥤ Over S :=
    (Stack.fibredCategory B S hS c.X').val.p ⋙ Over.post B.inclusion
  let qF := LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)
  let U : Over S := qF.obj x
  let U' : Over S := q𝒳.obj t.openObject
  let j : U'.left ⟶ U.left := ((Over.post B.inclusion).map t.openHom).left
  have : _root_.AlgebraicGeometry.IsOpenImmersion j :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion t.openPart.ι)
  let u' : U'.left := u
  have hjU : j ≫ U.hom = U'.hom := Over.w ((Over.post B.inclusion).map t.openHom)
  -- an affine open `Spec Λ ⊆ S` through which the residue point of `j u'` factors
  let i := S.affineOpenCover.idx (Deformation.Artin.basePoint U (j u'))
  let Λ := (S.affineOpenCover.X i : Type u)
  let iΛ : Spec (.of Λ) ⟶ S := S.affineOpenCover.f i
  have hcov : Deformation.Artin.basePoint U (j u') ∈ Set.range iΛ.base :=
    S.affineOpenCover.covers _
  have hres : Spec.map (j.residueFieldMap u') ≫ U.left.fromSpecResidueField (j u') =
      U'.left.fromSpecResidueField u' ≫ j :=
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField j u'
  have hcomp : U'.left.fromSpecResidueField u' ≫ U'.hom =
      Spec.map (j.residueFieldMap u') ≫ (U.left.fromSpecResidueField (j u') ≫ U.hom) := by
    rw [← hjU, ← Category.assoc, ← hres, Category.assoc]
  have H : Set.range (U.left.fromSpecResidueField (j u') ≫ U.hom).base ⊆
      Set.range iΛ.base := by
    rintro _ ⟨s, rfl⟩
    have hs : s = IsLocalRing.closedPoint (U.left.residueField (j u')) :=
      Subsingleton.elim (α := Spec (U.left.residueField (j u'))) _ _
    rw [hs]
    exact hcov
  have H' : Set.range (U'.left.fromSpecResidueField u' ≫ U'.hom).base ⊆ Set.range iΛ.base := by
    rw [hcomp, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact (Set.range_comp_subset_range _ _).trans H
  let algU : Algebra Λ (U.left.residueField (j u')) :=
    Deformation.Artin.chartResidueAlgebra iΛ U (j u') H
  let algU' : Algebra Λ (U'.left.residueField u') :=
    Deformation.Artin.chartResidueAlgebra iΛ U' u' H'
  have hcU := Deformation.Artin.algebraMap_chartResidueAlgebra iΛ U (j u') H
  have hcU' := Deformation.Artin.algebraMap_chartResidueAlgebra iΛ U' u' H'
  have hlin : ∀ l : Λ, (j.residueFieldMap u').hom
      (algebraMap Λ (U.left.residueField (j u') : Type u) l) =
      algebraMap Λ (U'.left.residueField u' : Type u) l := by
    have h : ((j.residueFieldMap u').hom.comp
        (algebraMap Λ (U.left.residueField (j u') : Type u))) =
        algebraMap Λ (U'.left.residueField u' : Type u) := by
      refine Deformation.Artin.ringHom_eq_of_specMap_comp_eq iΛ _ _ ?_
      have h₁ : CommRingCat.ofHom ((j.residueFieldMap u').hom.comp
          (algebraMap Λ (U.left.residueField (j u') : Type u))) =
          CommRingCat.ofHom (algebraMap Λ (U.left.residueField (j u') : Type u)) ≫
            j.residueFieldMap u' := rfl
      rw [h₁, Spec.map_comp, Category.assoc, hcU, ← Category.assoc, hres, Category.assoc, hjU,
        hcU']
    exact fun l => RingHom.congr_fun h l
  let e : (U.left.residueField (j u') : Type u) ≃ₐ[Λ] (U'.left.residueField u' : Type u) :=
    AlgEquiv.ofRingEquiv (f := (asIso (j.residueFieldMap u')).commRingCatIsoToRingEquiv) hlin
  have hespec : CommRingCat.ofHom e.toAlgHom.toRingHom = j.residueFieldMap u' := rfl
  have heq : U'.left.fromSpecResidueField u' ≫ j =
      Spec.map (CommRingCat.ofHom e.toAlgHom.toRingHom) ≫
        U.left.fromSpecResidueField (j u') := by
    rw [hespec]
    exact hres.symm
  refine (Deformation.Artin.isVersalAt_iff_liftsAtResiduePoint_chart iΛ U' u' q𝒳 t.openObject
    rfl hcU').trans ?_
  refine Iff.trans ?_ (Deformation.Artin.isVersalAt_iff_liftsAtResiduePoint_chart iΛ U (j u') qF
    x rfl hcU).symm
  refine (liftsAtResiduePoint_openObject_iff c (Λ := Λ) (k := U'.left.residueField u') iΛ x
    (U'.left.fromSpecResidueField u')).trans ?_
  refine Iff.trans ?_ (Deformation.Artin.liftsAtResiduePoint_iff_changeResidueField e iΛ
    qF U x rfl (U.left.fromSpecResidueField (j u'))).symm
  exact Iff.of_eq (congrArg (Deformation.Artin.LiftsAtResiduePoint iΛ qF U x rfl) heq)

end Artin.ContractionSituation

end AlgebraicGeometry

end
