module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Representability
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.RepresentabilitySizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceEtale

/-!
# Spaces of sections into a scheme over a finite locally free base

Let `U` be a scheme contained in a big fppf site, let `Z ⟶ U` be an object of the site over `U`
whose structure morphism is finite locally free, and let `v : V ⟶ Z` be a morphism of the site
whose source `V` is a scheme in which every finite set of points lies in an affine open — for
instance a disjoint union of affine schemes. This file proves that the space of sections of
`V ⟶ Z` over `U`, the functor `T ↦ {σ : Z_T ⟶ V_T a section}` of
`AlgebraicGeometry.Space.sectionSpace`, is an algebraic space over `U`.

This is the case of Stacks 05YF in which the restricted space is a scheme of the kind just
described and the base is a scheme; the general case reduces to it along an étale atlas.

## Main results

* `AlgebraicGeometry.Space.isRepresentable_prod_yoneda_of_isFiniteLocallyFree`: the functor
  `T ↦ Hom(Z × T, X)` of morphisms out of a finite locally free `Z` is representable on the big
  fppf site of `U`, whenever every finite set of points of a fibre of `X` lies in an affine open.
* `AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_yoneda`: the space of sections of
  `v : V ⟶ Z` is an algebraic space over `U`.
* `AlgebraicGeometry.Space.exists_isAffineOpen_finite_sigma`: a finite set of points of a disjoint
  union of affine schemes lies in an affine open.

## Implementation notes

The representability of `T ↦ Hom(Z × T, X)` is Stacks 0BL4, which is stated on the category of
all schemes over `U`. It is brought to the big fppf site along the fully faithful functor
`CategoryTheory.Over.post` of the inclusion of the site into all schemes, which preserves binary
products because the inclusion preserves fibre products; the representing scheme lies in the
site because of the size bound of
`Stacks.Morphisms.homFromFiniteLocallyFree_representableBy_size_le`.

The space of sections is then the fibre product of `T ↦ Hom(Z × T, V)` and of the final object
over `T ↦ Hom(Z × T, Z)`, the first map being composition with `v` and the second the first
projection: a section is a morphism `Z × T ⟶ V` whose composite with `v` is the projection.
Both functors over which the fibre product is taken are representable by the first result, so
the fibre product is an algebraic space by Stacks 02X2.

## References

* [Stacks Project, Tag 05YF](https://stacks.math.columbia.edu/tag/05YF)
* [Stacks Project, Tag 0BL4](https://stacks.math.columbia.edu/tag/0BL4)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w u₁ u₂ v₁ v₂

namespace CategoryTheory

/-- **Representability along a fully faithful functor.** If `Φ : C ⥤ D` is fully faithful and
`G : Dᵒᵖ ⥤ Type w` is represented by an object isomorphic to `Φ.obj Y`, then `Φ.op ⋙ G` is
represented by `Y`. -/
def Functor.RepresentableBy.ofFullyFaithful {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {Φ : C ⥤ D} (hΦ : Φ.FullyFaithful) {G : Dᵒᵖ ⥤ Type w} {Y : C} {Y' : D}
    (R : G.RepresentableBy Y') (e : Φ.obj Y ≅ Y') : (Φ.op ⋙ G).RepresentableBy Y where
  homEquiv {X} := hΦ.homEquiv.trans (e.homToEquiv.trans R.homEquiv)
  homEquiv_comp {X X'} f g := by
    change R.homEquiv ((Φ.map (f ≫ g)) ≫ e.hom) = G.map (Φ.map f).op (R.homEquiv (Φ.map g ≫ e.hom))
    rw [Φ.map_comp, Category.assoc, R.homEquiv_comp]

end CategoryTheory

namespace AlgebraicGeometry

/-! ### Finite sets of points in a disjoint union of affine schemes -/

open scoped Function in
/-- **A finite set of points of a disjoint union of affine schemes lies in an affine open**: the
union of the finitely many summands it meets is affine, being a finite disjoint union of affine
opens. -/
theorem exists_isAffineOpen_finite_sigma {σ : Type u} (g : σ → Scheme.{u})
    [∀ i, IsAffine (g i)] (t : Set (∐ g : Scheme.{u})) (ht : t.Finite) :
    ∃ O : (∐ g : Scheme.{u}).Opens, IsAffineOpen O ∧ t ⊆ O := by
  classical
  have hidx : ∀ x : (∐ g : Scheme.{u}), ∃ i, x ∈ (Sigma.ι g i).opensRange := fun x ↦ by
    obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk g).surjective x
    exact ⟨i, y, by rw [sigmaMk_mk]⟩
  choose idx hidx using hidx
  let E : Set σ := idx '' t
  have : Finite E := (ht.image idx).to_subtype
  let O : E → (∐ g : Scheme.{u}).Opens := fun i ↦ (Sigma.ι g i.1).opensRange
  exact ⟨iSup O, IsAffineOpen.iSup_of_disjoint (fun i ↦ isAffineOpen_opensRange _)
    (fun i j hij ↦ disjoint_opensRange_sigmaι g i.1 j.1 (fun h ↦ hij (Subtype.ext h))),
    fun x hx ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨⟨idx x, x, hx, rfl⟩, hidx x⟩⟩

/-- A scheme isomorphic to one in which every finite set of points lies in an affine open has
the same property. -/
theorem exists_isAffineOpen_finite_of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (hX : ∀ t : Set X, t.Finite → ∃ O : X.Opens, IsAffineOpen O ∧ t ⊆ O)
    (t : Set Y) (ht : t.Finite) : ∃ O : Y.Opens, IsAffineOpen O ∧ t ⊆ O := by
  obtain ⟨O, hO, htO⟩ := hX (e.inv '' t) (ht.image _)
  exact ⟨e.hom ''ᵁ O, hO.image_of_isOpenImmersion e.hom,
    fun y hy ↦ ⟨e.inv y, htO ⟨y, hy, rfl⟩, by simp⟩⟩

/-- **Over an affine morphism, every finite set of points of a fibre lies in an affine open**:
the preimage of an affine neighbourhood of the image point is affine. -/
theorem exists_isAffineOpen_fibre_of_isAffineHom {X S : Scheme.{u}} (g : X ⟶ S) [IsAffineHom g]
    (s : S) (t : Set X) (_ : t.Finite) (hts : ∀ x ∈ t, g.base x = s) :
    ∃ O : X.Opens, IsAffineOpen O ∧ t ⊆ O := by
  obtain ⟨-, ⟨W, hW, rfl⟩, hsW, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
  refine ⟨g ⁻¹ᵁ W, hW.preimage g, fun x hx ↦ ?_⟩
  change g.base x ∈ W
  exact hts x hx ▸ hsW

namespace Space

variable {B : BigFppfSite.{u}} {U : Scheme.{u}} {hU : B.Contains U}

/-! ### Morphisms out of a finite locally free object of the site -/

/-- The inclusion of the big fppf site of `U` into all schemes over `U`. -/
noncomputable abbrev overPostInclusion : BigFppfOver B U hU ⥤ Over U :=
  Over.post (X := B.obj hU) B.inclusion

/-- The inclusion `AlgebraicGeometry.Space.overPostInclusion` is full. -/
instance : (overPostInclusion (B := B) (U := U) (hU := hU)).Full :=
  inferInstanceAs (Over.post (X := B.obj hU) B.inclusion).Full

/-- The inclusion `AlgebraicGeometry.Space.overPostInclusion` is faithful. -/
instance : (overPostInclusion (B := B) (U := U) (hU := hU)).Faithful :=
  inferInstanceAs (Over.post (X := B.obj hU) B.inclusion).Faithful

/-- The inclusion `AlgebraicGeometry.Space.overPostInclusion` preserves binary products. -/
instance : PreservesLimitsOfShape (Discrete WalkingPair)
    (overPostInclusion (B := B) (U := U) (hU := hU)) := by
  have : PreservesLimitsOfShape WalkingCospan B.inclusion := inferInstance
  exact inferInstanceAs (PreservesLimitsOfShape (Discrete WalkingPair)
    (Over.post (X := B.obj hU) B.inclusion))

/-- Composition with the comparison of binary products commutes with base change along the
second factor, read through the fully faithful `AlgebraicGeometry.Space.overPostInclusion`. -/
theorem preimage_prodComparison_comp {Z X T T' : BigFppfOver B U hU} (f : T' ⟶ T)
    (b : (overPostInclusion (B := B) (U := U) (hU := hU)).obj Z ⨯
      (overPostInclusion (B := B) (U := U) (hU := hU)).obj T ⟶
        (overPostInclusion (B := B) (U := U) (hU := hU)).obj X) :
    (Functor.FullyFaithful.ofFullyFaithful overPostInclusion).preimage
        ((PreservesLimitPair.iso overPostInclusion Z T').hom ≫
          prod.map (𝟙 _) (overPostInclusion.map f) ≫ b) =
      prod.map (𝟙 Z) f ≫ (Functor.FullyFaithful.ofFullyFaithful overPostInclusion).preimage
        ((PreservesLimitPair.iso overPostInclusion Z T).hom ≫ b) := by
  let P := overPostInclusion (B := B) (U := U) (hU := hU)
  let hP : P.FullyFaithful := .ofFullyFaithful P
  apply hP.map_injective
  rw [P.map_comp, hP.map_preimage, hP.map_preimage, PreservesLimitPair.iso_hom,
    PreservesLimitPair.iso_hom, ← Category.assoc, ← Category.assoc, ← P.map_id,
    prodComparison_natural]

/-- Morphisms `Z × T ⟶ X` in the big fppf site of `U` are morphisms between the corresponding
schemes over `U`, naturally in `T`. -/
noncomputable def prodYonedaOverPostIso (Z X : BigFppfOver B U hU) :
    (overPostInclusion (B := B) (U := U) (hU := hU)).op ⋙
        ((prod.functor.obj ((overPostInclusion (B := B) (U := U) (hU := hU)).obj Z)).op ⋙
          yoneda.obj ((overPostInclusion (B := B) (U := U) (hU := hU)).obj X)) ≅
      (prod.functor.obj Z).op ⋙ yoneda.obj X :=
  NatIso.ofComponents (fun T ↦ Equiv.toIso
    ((PreservesLimitPair.iso overPostInclusion Z T.unop).homFromEquiv.symm.trans
      (Functor.FullyFaithful.ofFullyFaithful overPostInclusion).homEquiv.symm)) (by
    intro T T' f
    ext b
    exact preimage_prodComparison_comp f.unop b)

/-- **The functor `T ↦ Hom(Z × T, X)` on the big fppf site of `U` is representable** when the
structure morphism of `Z` is finite locally free and every finite set of points of a fibre of `X`
over `U` lies in an affine open of `X`.

This is Stacks 0BL4 brought to the site: the representing scheme over `U` lies in the site by the
size bound of `Stacks.Morphisms.homFromFiniteLocallyFree_representableBy_size_le`, and the
functor is the restriction of the corresponding functor on all schemes over `U` along the fully
faithful, product preserving `AlgebraicGeometry.Space.overPostInclusion`. -/
theorem isRepresentable_prod_yoneda_of_isFiniteLocallyFree (Z X : BigFppfOver B U hU)
    [Stacks.Morphisms.IsFiniteLocallyFree (B.inclusion.map Z.hom)]
    (hX : ∀ (s : U) (t : Set ((BigFppfOver.toScheme B U hU).obj X)), t.Finite →
      (∀ x ∈ t, (B.inclusion.map X.hom).base x = s) →
      ∃ O : ((BigFppfOver.toScheme B U hU).obj X).Opens, IsAffineOpen O ∧ t ⊆ O) :
    ((prod.functor.obj Z).op ⋙ yoneda.obj X).IsRepresentable := by
  let P := overPostInclusion (B := B) (U := U) (hU := hU)
  obtain ⟨M, hMs, ⟨R⟩⟩ := Stacks.Morphisms.homFromFiniteLocallyFree_representableBy_size_le
    (B.inclusion.map Z.hom) (B.inclusion.map X.hom) hX
  have hM : B.Contains M.left :=
    hMs.trans_lt (max_lt B.aleph0_lt_cutoff (max_lt hU X.left.property))
  let Ms : BigFppfOver B U hU :=
    Over.mk (B.inclusion.preimage (X := B.obj hM) (Y := B.obj hU) M.hom)
  let eM : P.obj Ms ≅ M := Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ M.hom = B.inclusion.map (B.inclusion.preimage (X := B.obj hM) (Y := B.obj hU)
      M.hom)
    rw [Functor.map_preimage, Category.id_comp])
  exact ((Functor.RepresentableBy.ofFullyFaithful (.ofFullyFaithful P) R eM).ofIso
    (prodYonedaOverPostIso Z X)).isRepresentable

/-- `T ↦ Hom(Z × T, X)` is an algebraic space over `U`, under the hypotheses of
`AlgebraicGeometry.Space.isRepresentable_prod_yoneda_of_isFiniteLocallyFree`. -/
theorem isAlgebraicSpace_prod_yoneda_of_isFiniteLocallyFree (Z X : BigFppfOver B U hU)
    [Stacks.Morphisms.IsFiniteLocallyFree (B.inclusion.map Z.hom)]
    (hX : ∀ (s : U) (t : Set ((BigFppfOver.toScheme B U hU).obj X)), t.Finite →
      (∀ x ∈ t, (B.inclusion.map X.hom).base x = s) →
      ∃ O : ((BigFppfOver.toScheme B U hU).obj X).Opens, IsAffineOpen O ∧ t ⊆ O) :
    IsAlgebraicSpace B U hU ((prod.functor.obj Z).op ⋙ yoneda.obj X) := by
  have := isRepresentable_prod_yoneda_of_isFiniteLocallyFree Z X hX
  exact AlgebraicGeometry.isAlgebraicSpace_of_iso B U hU
    (Functor.reprW ((prod.functor.obj Z).op ⋙ yoneda.obj X)).symm
    (isAlgebraicSpace_yoneda B U hU _)

/-! ### The space of sections into a scheme -/

/-- The morphism `T ↦ Hom(Z × T, V) ⟶ T ↦ Hom(Z × T, Z)` of composition with `v : V ⟶ Z`. -/
noncomputable def sectionAmbientPostcomp {Z V : BigFppfOver B U hU} (v : V ⟶ Z) :
    (prod.functor.obj Z).op ⋙ yoneda.obj V ⟶ (prod.functor.obj Z).op ⋙ yoneda.obj Z where
  app T := ↾fun b ↦ b ≫ v
  naturality T T' f := by
    ext b
    exact Category.assoc _ _ _

/-- The point of `T ↦ Hom(Z × T, Z)` given by the first projections. -/
noncomputable def sectionAmbientFst (Z : BigFppfOver B U hU) :
    yoneda.obj (Over.mk (𝟙 (B.obj hU))) ⟶ (prod.functor.obj Z).op ⋙ yoneda.obj Z where
  app T := ↾fun _ ↦ prod.fst
  naturality T T' f := by
    ext b
    exact (prod.map_fst _ _).trans (Category.comp_id _) |>.symm

/-- **The space of sections of `v : V ⟶ Z` is the fibre product** of `T ↦ Hom(Z × T, V)` and of
the final object over `T ↦ Hom(Z × T, Z)`: a section is a morphism `Z × T ⟶ V` whose composite with
`v` is the first projection. -/
theorem isPullback_sectionSpace_yoneda {Z V : BigFppfOver B U hU} (v : V ⟶ Z) :
    IsPullback
      ((sectionSpaceIsoSubfunctor Z (yoneda.obj V) (yoneda.map v)).hom ≫
        (sectionSubfunctor Z (yoneda.obj V) (yoneda.map v)).ι)
      (terminal.from _ ≫ (terminalIsoIsTerminal
        ((Over.mkIdTerminal (X := B.obj hU)).isTerminalObj yoneda _)).hom)
      (sectionAmbientPostcomp v) (sectionAmbientFst Z) := by
  have hT := (Over.mkIdTerminal (X := B.obj hU)).isTerminalObj yoneda _
  refine IsPullback.of_iso (fst := (sectionSubfunctor Z (yoneda.obj V) (yoneda.map v)).ι)
    (snd := terminal.from _ ≫ (terminalIsoIsTerminal hT).hom)
    (f := sectionAmbientPostcomp v) (g := sectionAmbientFst Z) ?_
    (sectionSpaceIsoSubfunctor Z (yoneda.obj V) (yoneda.map v)).symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (by simp) (hT.hom_ext _ _) ((Category.comp_id _).trans (Category.id_comp _).symm)
    (by simp)
  refine IsPullback.of_forall_isPullback_app fun T ↦ ?_
  rw [Limits.Types.isPullback_iff]
  refine ⟨?_, fun s s' h ↦ Subtype.ext h.1, fun b t hbt ↦
    ⟨⟨b, hbt⟩, rfl, (Over.mkIdTerminal (X := B.obj hU)).hom_ext _ _⟩⟩
  ext s
  exact s.2

/-- **The space of sections of `v : V ⟶ Z` over `U` is an algebraic space** when the structure
morphism of `Z` is finite locally free and every finite set of points of `V` lies in an affine
open: it is the fibre product of `AlgebraicGeometry.Space.isPullback_sectionSpace_yoneda`, whose
three other corners are representable by
`AlgebraicGeometry.Space.isRepresentable_prod_yoneda_of_isFiniteLocallyFree`, the target `Z`
satisfying the hypothesis on finite sets because it is affine over `U`. -/
theorem isAlgebraicSpace_sectionSpace_yoneda {Z V : BigFppfOver B U hU} (v : V ⟶ Z)
    [Stacks.Morphisms.IsFiniteLocallyFree (B.inclusion.map Z.hom)]
    (hV : ∀ t : Set ((BigFppfOver.toScheme B U hU).obj V), t.Finite →
      ∃ O : ((BigFppfOver.toScheme B U hU).obj V).Opens, IsAffineOpen O ∧ t ⊆ O) :
    IsAlgebraicSpace B U hU (sectionSpace B U hU Z (yoneda.obj V) (yoneda.map v)) := by
  have hZ : _root_.AlgebraicGeometry.IsAffineHom (B.inclusion.map Z.hom) := inferInstance
  exact AlgebraicGeometry.isAlgebraicSpace_of_iso B U hU
    (isPullback_sectionSpace_yoneda v).isoPullback
    (isAlgebraicSpace_pullback B U hU _ _
      (isAlgebraicSpace_prod_yoneda_of_isFiniteLocallyFree Z V
        (fun _ t ht _ ↦ hV t ht))
      (isAlgebraicSpace_yoneda B U hU _)
      (isAlgebraicSpace_prod_yoneda_of_isFiniteLocallyFree Z Z
        (exists_isAffineOpen_fibre_of_isAffineHom _)))

end Space

end AlgebraicGeometry

end
