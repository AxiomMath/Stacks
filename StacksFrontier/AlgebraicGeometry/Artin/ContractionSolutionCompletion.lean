module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionLocus
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionMorphismsAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismUniquenessAlongClosedSubset

/-!
# The comparison map from the completion of a solution to `W`

Let `c` be a contraction situation `AlgebraicGeometry.Artin.ContractionSituation` and let `X` be
a presheaf on the big fppf site of `S` carrying a functorial bijection `F(V) = Mor_S(V, X)` on the
locally Noetherian schemes `V` over `S`, where `F` is Artin's functor. Let `T ⊆ |X|` be
`AlgebraicGeometry.Artin.ContractionSituation.contractedLocus`. A morphism `ξ : V ⟶ X` has
point-set image in `T` exactly when the triple `(Z, u', x̂)` matching it has `Z = |V|`; for such a
triple `V_{/Z} = V`, and evaluating `x̂` at the identity of `V` gives a section of `W` over `V`.
These sections assemble into a morphism of functors on locally Noetherian schemes over `S`, from
the sections of `X` with point-set image in `T` to `W`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.completionIdSection`: the tautological section of `V_{/Z}`
  over `V` when `Z` is all of `|V|`, that is of `V_{/V} = V`.
* `AlgebraicGeometry.FormalSpace.completionIdHom` and
  `AlgebraicGeometry.FormalSpace.completionSheafUnivHomEquiv`: the morphism `V_{/V} ⟶ Y` into
  a sheaf determined by a section of `Y` over `V`, and the resulting bijection between those
  morphisms and those sections — the precise form of `V_{/V} = V`.
* `AlgebraicGeometry.Artin.ContractionSituation.wSection`: the section of `W` over `V` that a
  triple over `V` whose closed subset is all of `|V|` determines.
* `AlgebraicGeometry.Artin.ContractionSituation.completionSectionToW`: the section of `W` over
  a locally Noetherian scheme `V` over `S` attached to a section of `X` over `V` whose
  point-set image lies in `T`.
* `AlgebraicGeometry.Artin.ContractionSituation.completionToW`: those sections assembled into
  a morphism of functors on locally Noetherian schemes over `S`, from the sections of `X` with
  point-set image in `T` to `W`.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.tripleOfMor_Z_eq_univ_iff` and
  `AlgebraicGeometry.Artin.ContractionSituation.hasImageIn_contractedLocus_iff`: for a locally
  Noetherian scheme `V` over `S` and a morphism `ξ : V ⟶ X`, the point-set image of `ξ` is
  contained in `T` exactly when the closed subset `Z` of the triple matching `ξ` is all of `|V|`.
* `AlgebraicGeometry.Artin.ContractionSituation.wSection_mapTriple`: the section of `W`
  determined by a triple is compatible with transport of triples.
* `AlgebraicGeometry.Artin.ContractionSituation.completionSectionToW_map`: naturality of the
  comparison map on sections.
* `AlgebraicGeometry.FormalSpace.completionSheaf_hom_ext_of_univ`: a morphism out of
  `V_{/V}` is determined by its value at the tautological section.
* `AlgebraicGeometry.Artin.ContractionSituation.wSection_eq_iff`: the fibres of the comparison
  map: a triple whose closed subset is all of `|V|` matches a prescribed section `w` of `W`
  exactly when its third component is the morphism `V_{/V} = V ⟶ W` corresponding to `w`.

## References

* [Stacks Project, Tag 03BY](https://stacks.math.columbia.edu/tag/03BY)
* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
* [Stacks Project, Tag 0GDU](https://stacks.math.columbia.edu/tag/0GDU)
* [Stacks Project, Tag 0GE3](https://stacks.math.columbia.edu/tag/0GE3)
* [Stacks Project, Tag 0GE4](https://stacks.math.columbia.edu/tag/0GE4)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GHA](https://stacks.math.columbia.edu/tag/0GHA)
* [Stacks Project, Tag 0GHC](https://stacks.math.columbia.edu/tag/0GHC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- Every section of a presheaf has point-set image in the whole space of points of that
presheaf: the condition is that certain points lie in `Set.univ`. -/
theorem hasImageIn_univ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (U : BigFppfOver B S hS)
    (x : X.obj (op U)) : HasImageIn B S hS X Set.univ U x :=
  fun _ => Set.mem_univ _

end Space

namespace FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.pointTopology

/-- The section of a completion given by a section of the ambient presheaf depends only on
that section, not on the witness that its point-set image lies in the set. -/
theorem presheafSection_congr {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : Set (Space.points B S hS F)} {U : BigFppfOver B S hS} {x y : F.obj (op U)} (h : x = y)
    (hx : Space.HasImageIn B S hS F T U x) (hy : Space.HasImageIn B S hS F T U y) :
    presheafSection B S hS x hx = presheafSection B S hS y hy := by
  subst h; rfl

/-- Restricting a completion along a morphism of presheaves carries the section given by a
section of the source into the section given by its image. -/
theorem completionSheafRestrict_presheafSection {F' F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F' ⟶ F) (T' : Set (Space.points B S hS F')) (T : Set (Space.points B S hS F))
    (h : T' ⊆ Space.pointsMap B S hS F' f ⁻¹' T) {U : BigFppfOver B S hS}
    (x : F'.obj (op U)) (hx : Space.HasImageIn B S hS F' T' U x)
    (hx' : Space.HasImageIn B S hS F T U (f.app (op U) x)) :
    (Space.completionSheafRestrict B S hS f T' T h).hom.app (op U)
        (presheafSection B S hS x hx) =
      presheafSection B S hS (f.app (op U) x) hx' :=
  (NatTrans.congr_app ((BigFppfOver.topology B S hS).toSheafify_naturality
    (Space.completionSubfunctorRestrict B S hS f T' T h)) (op U) ▸ rfl :
      ((BigFppfOver.topology B S hS).toSheafify _ ≫
        (BigFppfOver.topology B S hS).sheafifyMap
          (Space.completionSubfunctorRestrict B S hS f T' T h)).app (op U)
            ⟨ULift.up x, hx⟩ = _)

/-- The tautological section of the completion of a representable presheaf `V` along a set of
points that is all of `|V|`: in that case `V_{/Z}` is `V`, and the section is the identity of
`V`. -/
noncomputable def completionIdSection (V : BigFppfOver B S hS)
    (Z : Set (Space.points B S hS (yoneda.obj V))) (hZ : Z = Set.univ) :
    (Space.completionSheaf B S hS (yoneda.obj V) Z).obj.obj (op V) :=
  presheafSection B S hS (𝟙 V) (hZ ▸ Space.hasImageIn_univ B S hS (yoneda.obj V) V (𝟙 V))

/-- Every section of a representable presheaf has point-set image in a set of points that is
all of the points. -/
private theorem hasImageIn_of_eq_univ {V : BigFppfOver B S hS}
    {Z : Set (Space.points B S hS (yoneda.obj V))} (hZ : Z = Set.univ) (U : BigFppfOver B S hS)
    (x : U ⟶ V) : Space.HasImageIn B S hS (yoneda.obj V) Z U x :=
  hZ ▸ Space.hasImageIn_univ B S hS (yoneda.obj V) U x

/-- The tautological section of `V_{/Z}` for `Z` all of `|V|` is natural: restricting it
along `φ : V₂ ⟶ V₁` gives the tautological section of `V_{2,/Z₂}`. -/
theorem completionIdSection_restrict {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁)
    (Z₁ : Set (Space.points B S hS (yoneda.obj V₁))) (hZ₁ : Z₁ = Set.univ)
    (Z₂ : Set (Space.points B S hS (yoneda.obj V₂))) (hZ₂ : Z₂ = Set.univ)
    (h : Z₂ ⊆ Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹' Z₁) :
    (Space.completionSheafRestrict B S hS (yoneda.map φ) Z₂ Z₁ h).hom.app (op V₂)
        (completionIdSection B S hS V₂ Z₂ hZ₂) =
      (Space.completionSheaf B S hS (yoneda.obj V₁) Z₁).obj.map φ.op
        (completionIdSection B S hS V₁ Z₁ hZ₁) := by
  have hφ := hasImageIn_of_eq_univ B S hS hZ₁ V₂ φ
  have hleft : (yoneda.map φ).app (op V₂) (𝟙 V₂) = φ := by simp
  have hright : (yoneda.obj V₁).map φ.op (𝟙 V₁) = φ := by simp
  rw [completionIdSection, completionIdSection,
    completionSheafRestrict_presheafSection B S hS (yoneda.map φ) Z₂ Z₁ h (𝟙 V₂) _
      (by rw [hleft]; exact hφ),
    presheafSection_map B S hS (F := yoneda.obj V₁) (TF := Z₁) φ (𝟙 V₁) _
      (by rw [hright]; exact hφ),
    presheafSection_congr B S hS hleft _ hφ, presheafSection_congr B S hS hright _ hφ]

/-- The morphism of presheaves out of the completion subfunctor of `V` along all of `|V|`
determined by a section `y` of a sheaf `Y` over `V`: a section of that subfunctor over `U` is
a morphism `f : U ⟶ V`, and it is sent to the restriction of `y` along `f`. -/
def completionIdSubfunctorHom (V : BigFppfOver B S hS)
    (Z : Set (Space.points B S hS (yoneda.obj V)))
    {Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} (y : Y.obj.obj (op V)) :
    (Space.completionSubfunctor B S hS (yoneda.obj V) Z).toFunctor ⟶ Y.obj where
  app U := ↾fun s => Y.obj.map s.1.down.op y
  naturality U U' i := by
    ext s
    change Y.obj.map (i.unop ≫ s.1.down).op y = Y.obj.map i (Y.obj.map s.1.down.op y)
    rw [op_comp, Y.obj.map_comp]
    rfl

/-- The morphism out of the completion of `V` along all of `|V|` determined by a section `y`
of a sheaf `Y` over `V`, by the universal property of sheafification. -/
noncomputable def completionIdHom (V : BigFppfOver B S hS)
    (Z : Set (Space.points B S hS (yoneda.obj V))) (_hZ : Z = Set.univ)
    {Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} (y : Y.obj.obj (op V)) :
    Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ Y :=
  ObjectProperty.homMk ((BigFppfOver.topology B S hS).sheafifyLift
    (completionIdSubfunctorHom B S hS V Z y) Y.property)

/-- A morphism out of the completion of `V` along all of `|V|` into a sheaf is determined by
its value at the tautological section. -/
theorem completionSheaf_hom_ext_of_univ {V : BigFppfOver B S hS}
    (Z : Set (Space.points B S hS (yoneda.obj V))) (hZ : Z = Set.univ)
    {Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    {Φ Ψ : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ Y}
    (h : Φ.hom.app (op V) (completionIdSection B S hS V Z hZ) =
      Ψ.hom.app (op V) (completionIdSection B S hS V Z hZ)) :
    Φ = Ψ := by
  have hid := hasImageIn_of_eq_univ B S hS hZ V (𝟙 V)
  apply Sheaf.hom_ext
  apply (BigFppfOver.topology B S hS).sheafify_hom_ext _ _ Y.property
  ext U s
  obtain ⟨⟨f⟩, hf⟩ := s
  have key (Θ : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ Y) :
      ((BigFppfOver.topology B S hS).toSheafify
        (Space.completionSubfunctor B S hS (yoneda.obj V) Z).toFunctor ≫ Θ.hom).app U
          ⟨ULift.up f, hf⟩ =
        Y.obj.map f.op (Θ.hom.app (op V) (completionIdSection B S hS V Z hZ)) :=
    (congrArg _ (Subtype.ext (ULift.ext (Category.comp_id f).symm))).trans
      (NatTrans.naturality_apply ((BigFppfOver.topology B S hS).toSheafify
        (Space.completionSubfunctor B S hS (yoneda.obj V) Z).toFunctor ≫ Θ.hom)
        (X := op V) (Y := U) f.op ⟨ULift.up (𝟙 V), hid⟩)
  exact (key Φ).trans ((congrArg _ h).trans (key Ψ).symm)

/-- The value of `AlgebraicGeometry.FormalSpace.completionIdHom` at the tautological section
is the section it was built from. -/
theorem completionIdHom_completionIdSection (V : BigFppfOver B S hS)
    (Z : Set (Space.points B S hS (yoneda.obj V))) (hZ : Z = Set.univ)
    {Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))} (y : Y.obj.obj (op V)) :
    (completionIdHom B S hS V Z hZ y).hom.app (op V)
        (completionIdSection B S hS V Z hZ) = y := by
  have hid := hasImageIn_of_eq_univ B S hS hZ V (𝟙 V)
  have h := NatTrans.congr_app ((BigFppfOver.topology B S hS).toSheafify_sheafifyLift
    (completionIdSubfunctorHom B S hS V Z y) Y.property) (op V)
  show ((BigFppfOver.topology B S hS).toSheafify
      (Space.completionSubfunctor B S hS (yoneda.obj V) Z).toFunctor ≫
      (BigFppfOver.topology B S hS).sheafifyLift
        (completionIdSubfunctorHom B S hS V Z y) Y.property).app (op V)
          (⟨ULift.up (𝟙 V), hid⟩ :
            (Space.completionSubfunctor B S hS (yoneda.obj V) Z).toFunctor.obj (op V)) = y
  rw [h]
  show Y.obj.map (𝟙 V).op y = y
  simp

/-- Morphisms from the completion of `V` along all of `|V|` into a sheaf `Y` are the sections
of `Y` over `V`. -/
noncomputable def completionSheafUnivHomEquiv (V : BigFppfOver B S hS)
    (Z : Set (Space.points B S hS (yoneda.obj V))) (hZ : Z = Set.univ)
    (Y : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) :
    (Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ Y) ≃ Y.obj.obj (op V) where
  toFun Φ := Φ.hom.app (op V) (completionIdSection B S hS V Z hZ)
  invFun y := completionIdHom B S hS V Z hZ y
  left_inv _ := completionSheaf_hom_ext_of_univ B S hS Z hZ
    (completionIdHom_completionIdSection B S hS V Z hZ _)
  right_inv y := completionIdHom_completionIdSection B S hS V Z hZ y

end FormalSpace

namespace Artin.ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS)

attribute [local instance] Space.pointTopology

/-! ### The section of `W` determined by a triple whose closed subset is everything -/

/-- The section of `W` over `V` determined by a triple `(Z, u', x̂)` over `V` whose closed
subset `Z` is all of `|V|`: then `V_{/Z} = V`, and the section is the value of `x̂` at the
tautological section `AlgebraicGeometry.FormalSpace.completionIdSection`. -/
noncomputable def wSection {V : BigFppfOver B S hS} (t : Triple c V) (ht : t.Z = Set.univ) :
    c.W.obj.obj (op V) :=
  t.xhat.hom.app (op V) (FormalSpace.completionIdSection B S hS V t.Z ht)

/-- The section of `W` determined by a triple depends only on the triple, not on the witness
that its closed subset is everything. -/
theorem wSection_congr {V : BigFppfOver B S hS} {t t' : Triple c V} (h : t = t')
    (ht : t.Z = Set.univ) (ht' : t'.Z = Set.univ) :
    wSection c t ht = wSection c t' ht' := by
  subst h; rfl

/-- The section of `W` determined by a triple is compatible with the transport of triples:
transporting a triple along `φ : V₂ ⟶ V₁` restricts its section along `φ`. -/
theorem wSection_mapTriple {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁) (t : Triple c V₁)
    (ht : t.Z = Set.univ) (ht₂ : (mapTriple c φ t).Z = Set.univ) :
    wSection c (mapTriple c φ t) ht₂ = c.W.obj.map φ.op (wSection c t ht) := by
  show t.xhat.hom.app (op V₂)
      ((Space.completionSheafRestrict B S hS (yoneda.map φ) (mapTriple c φ t).Z t.Z
        (mapTriple_Z_eq_preimage c φ t).subset).hom.app (op V₂)
          (FormalSpace.completionIdSection B S hS V₂ (mapTriple c φ t).Z ht₂)) = _
  rw [FormalSpace.completionIdSection_restrict B S hS φ t.Z ht (mapTriple c φ t).Z ht₂,
    NatTrans.naturality_apply t.xhat.hom φ.op]
  rfl

/-- The section of `W` determined by a triple is its third component, read through the
Yoneda identification `V_{/V} = V` of
`AlgebraicGeometry.FormalSpace.completionSheafUnivHomEquiv`. -/
theorem wSection_eq_completionSheafUnivHomEquiv {V : BigFppfOver B S hS} (t : Triple c V)
    (ht : t.Z = Set.univ) :
    wSection c t ht =
      FormalSpace.completionSheafUnivHomEquiv B S hS V t.Z ht c.W t.xhat := rfl

/-- A triple whose closed subset is all of `|V|` determines a prescribed section `w` of `W`
exactly when its third component is the morphism `V_{/V} = V ⟶ W` that `w` corresponds to
under the Yoneda identification. -/
theorem wSection_eq_iff {V : BigFppfOver B S hS} (t : Triple c V) (ht : t.Z = Set.univ)
    (w : c.W.obj.obj (op V)) :
    wSection c t ht = w ↔ t.xhat = FormalSpace.completionIdHom B S hS V t.Z ht w :=
  (FormalSpace.completionSheafUnivHomEquiv B S hS V t.Z ht c.W).apply_eq_iff_eq_symm_apply

/-! ### Sections with point-set image in `T` -/

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (α : contractionFunctor c ≅ morOnLocallyNoetherian B S hS X)

/-- For a locally Noetherian scheme `V` over `S` and a morphism `ξ : V ⟶ X`, the closed subset
`Z` of the triple `(Z, u', x̂)` that the functorial bijection matches with `ξ` is all of `|V|`
exactly when the point-set image of `ξ` is contained in the subset `T ⊆ |X|` of the
solution. -/
theorem tripleOfMor_Z_eq_univ_iff (V : LocallyNoetherianOver B S hS)
    (ξ : yoneda.obj V.obj ⟶ X) :
    (tripleOfMor c α V ξ).Z = Set.univ ↔
      Set.range (Space.pointsMap B S hS (yoneda.obj V.obj) ξ) ⊆ contractedLocus c α := by
  rw [← preimage_contractedLocus c α V ξ, Set.preimage_eq_univ_iff]

/-- A section of `X` over a locally Noetherian scheme `V` over `S` has point-set image in the
subset `T ⊆ |X|` of the solution exactly when the triple matching it has closed subset all of
`|V|`. -/
theorem hasImageIn_contractedLocus_iff (V : LocallyNoetherianOver B S hS)
    (x : X.obj (op V.obj)) :
    Space.HasImageIn B S hS X (contractedLocus c α) V.obj x ↔
      (tripleOfMor c α V (yonedaEquiv.symm x)).Z = Set.univ := by
  rw [tripleOfMor_Z_eq_univ_iff, Space.hasImageIn_iff_range_subset]

/-! ### The comparison map `X_{/T} ⟶ W` on locally Noetherian schemes -/

/-- The section of `W` over a locally Noetherian scheme `V` over `S` attached to a section of
`X` over `V` whose point-set image lies in the subset `T ⊆ |X|` of the solution: the section
determined by the triple matching it, whose closed subset is all of `|V|`. -/
noncomputable def completionSectionToW (V : LocallyNoetherianOver B S hS)
    (x : X.obj (op V.obj))
    (hx : Space.HasImageIn B S hS X (contractedLocus c α) V.obj x) :
    c.W.obj.obj (op V.obj) :=
  wSection c (tripleOfMor c α V (yonedaEquiv.symm x))
    ((hasImageIn_contractedLocus_iff c α V x).mp hx)

/-- The triple matching a restricted section is the transport of the triple matching the
section. -/
theorem tripleOfMor_map {V₂ V₁ : LocallyNoetherianOver B S hS} (φ : V₂ ⟶ V₁)
    (x : X.obj (op V₁.obj)) :
    tripleOfMor c α V₂ (yonedaEquiv.symm (X.map φ.hom.op x)) =
      mapTriple c φ.hom (tripleOfMor c α V₁ (yonedaEquiv.symm x)) := by
  simp only [tripleOfMor, Equiv.apply_symm_apply]
  exact inv_app_up_eq_mapTriple c α φ.hom x (X.map φ.hom.op x) rfl

/-- Naturality of the comparison map on sections: restricting a section of `X` with point-set
image in `T` along `φ : V₂ ⟶ V₁` restricts the attached section of `W` along `φ`. -/
theorem completionSectionToW_map {V₂ V₁ : LocallyNoetherianOver B S hS} (φ : V₂ ⟶ V₁)
    (x : X.obj (op V₁.obj))
    (hx : Space.HasImageIn B S hS X (contractedLocus c α) V₁.obj x)
    (hx' : Space.HasImageIn B S hS X (contractedLocus c α) V₂.obj (X.map φ.hom.op x)) :
    completionSectionToW c α V₂ (X.map φ.hom.op x) hx' =
      c.W.obj.map φ.hom.op (completionSectionToW c α V₁ x hx) := by
  rw [completionSectionToW, completionSectionToW,
    wSection_congr c (tripleOfMor_map c α φ x) _
      (by rw [← tripleOfMor_map c α φ x]
          exact (hasImageIn_contractedLocus_iff c α V₂ (X.map φ.hom.op x)).mp hx'),
    wSection_mapTriple]

/-- The comparison map on sections is the third component of the matching triple, read
through the Yoneda identification `V_{/V} = V`. -/
theorem completionSectionToW_eq_completionSheafUnivHomEquiv
    (V : LocallyNoetherianOver B S hS) (x : X.obj (op V.obj))
    (hx : Space.HasImageIn B S hS X (contractedLocus c α) V.obj x) :
    completionSectionToW c α V x hx =
      FormalSpace.completionSheafUnivHomEquiv B S hS V.obj
        (tripleOfMor c α V (yonedaEquiv.symm x)).Z
        ((hasImageIn_contractedLocus_iff c α V x).mp hx) c.W
        (tripleOfMor c α V (yonedaEquiv.symm x)).xhat := rfl

/-- The comparison morphism from the sections of `X` with point-set image in the subset
`T ⊆ |X|` of the solution to `W`, as functors on the locally Noetherian schemes over `S`. -/
noncomputable def completionToW :
    (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op ⋙
        (Space.completionSubfunctor B S hS X (contractedLocus c α)).toFunctor ⟶
      (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op ⋙ c.W.obj where
  app V := ↾fun s => completionSectionToW c α V.unop s.1.down s.2
  naturality V₁ V₂ φ := by
    ext s
    exact completionSectionToW_map c α φ.unop s.1.down s.2
      ((Space.completionSubfunctor B S hS X (contractedLocus c α)).map φ.unop.hom.op s.2 :)

end Artin.ContractionSituation

end AlgebraicGeometry

end
