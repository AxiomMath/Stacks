module

public import StacksFrontier.AlgebraicGeometry.ConormalComparison.Locality
public import
  StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.LocalCompleteIntersectionAffine
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.FiberRankIsomorphismInvariant
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekLocalCompleteIntersection.Restriction
public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantRank
public import StacksFrontier.AlgebraicGeometry.Modules.ReducedFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Implications
public import
  StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayRelativeDimensionOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.RelativeDimensionStrata
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.ConormalSequence
public import StacksFrontier.Topology.Sheaves.Modules.FiniteLocallyFreePresentation

/-!
# The map `∧^r Ω_{X/Y} ⟶ ω_{X/Y}` of [Stacks, Tag 0E9Z]

Let `f : X ⟶ Y` be a local complete intersection morphism of `FTS S`, `S` Noetherian, which
factors as an immersion `ι : X ⟶ P` followed by a proper smooth morphism `g : P ⟶ Y`. The
relative dimension `d` of `g` and the rank `c` of the conormal sheaf of `ι` are locally constant,
and on each of the open and closed pieces of `X` where they are constant, `f` is the composite of
a Koszul-regular closed immersion with conormal sheaf of rank `c`, an open immersion and a proper
morphism smooth of relative dimension `d`. This gives the locally constant function `r = d - c`
with `H^{-r}(f^!𝒪_Y)` the only nonzero cohomology sheaf of `f^!𝒪_Y`, and on each piece a map
`∧^r Ω_{X/Y} ⟶ H^{-r}(f^!𝒪_Y)` whose stalk at `x` is an isomorphism exactly when `f` is smooth
at `x`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality.ClosedOpenProperFactorization

section Immersion

variable {X P : Scheme.{u}} (ι : X ⟶ P) [IsImmersion ι]

/-- The restriction of an immersion over an open contained in its coborder is a closed
immersion. -/
theorem isClosedImmersion_morphismRestrict (O : P.Opens) (hO : O ≤ ι.coborderRange) :
    IsClosedImmersion (ι ∣_ O) := by
  refine .of_isPreimmersion _ ?_
  have hc : IsClosed ((Subtype.val : coborder (Set.range ι) → P) ⁻¹' Set.range ι) :=
    isClosed_preimage_val_coborder
  let incl : O → coborder (Set.range ι) := fun p ↦ ⟨p.1, hO p.2⟩
  have key : Set.range (ι ∣_ O) = incl ⁻¹' ((Subtype.val : coborder (Set.range ι) → P) ⁻¹'
      Set.range ι) := by
    ext p
    simp only [Set.mem_range, incl]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, (morphismRestrict_base_coe ι O x).symm⟩
    · rintro ⟨x, hx⟩
      exact ⟨⟨x, show ι x ∈ O from hx ▸ p.2⟩,
        Subtype.ext ((morphismRestrict_base_coe ι O _).trans hx)⟩
  rw [key]
  exact hc.preimage (by fun_prop)

/-- **The conormal sheaf of an immersion restricted to the preimage of an open.** For an open
`O ⊆ P` and a factorization `i ≫ e = ι ∣_ O` through an open immersion `e`, the restriction of
`𝒞_ι` to `ι⁻¹(O)` is the conormal sheaf of `i`. -/
def conormalSheafRestrictIsoOfFac (O : P.Opens) {W : Scheme.{u}} (e : W ⟶ O.toScheme)
    [IsOpenImmersion e] (i : (ι ⁻¹ᵁ O).toScheme ⟶ W) [IsImmersion i] (h : i ≫ e = ι ∣_ O) :
    (Scheme.Modules.restrictFunctor (ι ⁻¹ᵁ O).ι).obj (Stacks.Conormal.conormalSheaf ι) ≅
      Stacks.Conormal.conormalSheaf i :=
  (Scheme.Modules.restrictFunctor (ι ⁻¹ᵁ O).ι).mapIso
      (Stacks.Conormal.pullbackIdealSheafIsoOfCompEq ι.liftCoborder ι.coborderRange.ι ι
        ι.liftCoborder_ι).symm ≪≫
    Stacks.Conormal.Locality.conormalRestrictIso ι O ≪≫
    Stacks.Conormal.pullbackIdealSheafIsoOfCompEq i e (ι ∣_ O) h ≪≫
    Stacks.Conormal.pullbackIdealSheafIsoOfCompEq i.liftCoborder i.coborderRange.ι i
      i.liftCoborder_ι

end Immersion

section Strata

variable {P Y : Scheme.{u}} (g : P ⟶ Y) [Smooth g]

/-- The open and closed locus of `P` where the smooth morphism `g` has relative dimension `d`. -/
abbrev dimensionOpen (d : ℕ) : P.Opens :=
  relativeDimensionOpen g (isCohenMacaulay_fiber_of_smooth g) d

/-- The inclusion of the locus of relative dimension `d` of `g` is a closed immersion. -/
instance isClosedImmersion_dimensionOpen_ι (d : ℕ) : IsClosedImmersion (dimensionOpen g d).ι :=
  .of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact (relativeDimensionOpen_isClopen g (isCohenMacaulay_fiber_of_smooth g) d).1)

/-- The restriction of a proper `g` to its locus of relative dimension `d` is proper. -/
instance isProper_dimensionOpen_ι_comp [IsProper g] (d : ℕ) :
    IsProper ((dimensionOpen g d).ι ≫ g) := inferInstance

/-- The restriction of `g` to its locus of relative dimension `d` is smooth of relative
dimension `d`. -/
instance smoothOfRelativeDimension_dimensionOpen_ι_comp (d : ℕ) :
    SmoothOfRelativeDimension d ((dimensionOpen g d).ι ≫ g) :=
  smoothOfRelativeDimension_relativeDimensionOpen g d

end Strata

section Piece

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  {P : Scheme.{u}} (ι : X.left ⟶ P) [IsImmersion ι] (g : P ⟶ Y.left) [Smooth g] [IsProper g]
  (hfac : ι ≫ g = f.left) (d : ℕ) (O : P.Opens) (hOd : O ≤ dimensionOpen g d)
  (hOc : O ≤ ι.coborderRange)

/-- The open `ι⁻¹(O)` of `X` as an object of `FTS S`. -/
abbrev pieceFTS : FTS S := FTS.mk ((ι ⁻¹ᵁ O).ι ≫ X.hom)

/-- The inclusion of `ι⁻¹(O)` as a morphism of `FTS S`. -/
abbrev pieceHom : pieceFTS ι O ⟶ X := MorphismProperty.Over.homMk (ι ⁻¹ᵁ O).ι rfl

/-- The inclusion of `ι⁻¹(O)` into `X` is an open immersion. -/
instance isOpenImmersion_pieceHom_left : IsOpenImmersion (pieceHom ι O).left :=
  inferInstanceAs (IsOpenImmersion (ι ⁻¹ᵁ O).ι)

/-- The open `O` of `P`, read in the locus of relative dimension `d` of `g`. -/
abbrev pieceOpen : (dimensionOpen g d).toScheme.Opens := (dimensionOpen g d).ι ⁻¹ᵁ O

/-- The closed immersion `ι⁻¹(O) ⟶ O` given by `ι`. -/
def pieceImmersion : (ι ⁻¹ᵁ O).toScheme ⟶ (pieceOpen g d O).toScheme :=
  ι ∣_ O ≫ (Scheme.Opens.isoOfLE hOd).inv

include hOc in
omit [AlgebraicGeometry.IsNoetherian S] [IsProper g] in
/-- If `O` lies in the coborder of `ι`, then `ι⁻¹(O) ⟶ O` is a closed immersion. -/
theorem isClosedImmersion_pieceImmersion : IsClosedImmersion (pieceImmersion ι g d O hOd) := by
  have := isClosedImmersion_morphismRestrict ι O hOc
  unfold pieceImmersion
  infer_instance

omit [AlgebraicGeometry.IsNoetherian S] [IsImmersion ι] [IsProper g] in
/-- Composing `ι⁻¹(O) ⟶ O` with the identification of `O` as an open of `P` recovers the
restriction `ι ∣_ O`. -/
theorem pieceImmersion_comp_isoOfLE_hom :
    pieceImmersion ι g d O hOd ≫ (Scheme.Opens.isoOfLE hOd).hom = ι ∣_ O := by
  simp [pieceImmersion]

include hfac in
omit [IsImmersion ι] [IsProper g] in
/-- The composite of `ι⁻¹(O) ⟶ O` with the inclusions `O ⟶ P` and `g : P ⟶ Y` is the
restriction of `f` to `ι⁻¹(O)`. -/
theorem pieceImmersion_fac :
    pieceImmersion ι g d O hOd ≫ (pieceOpen g d O).ι ≫ (dimensionOpen g d).ι ≫ g =
      (pieceHom ι O ≫ f).left := by
  change _ = (ι ⁻¹ᵁ O).ι ≫ f.left
  rw [← hfac, ← morphismRestrict_ι_assoc]
  simp [pieceImmersion]

include hfac hOc in
omit [IsProper g] in
/-- If `f` is a local complete intersection morphism, then `ι⁻¹(O) ⟶ O` is a Koszul-regular
immersion. -/
theorem isKoszulRegularImmersion_pieceImmersion
    (hlci : IsLocalCompleteIntersectionMorphism f.left) :
    haveI := isClosedImmersion_pieceImmersion ι g d O hOd hOc
    Stacks.AlgebraicGeometry.RegularIdealSheaf.IsKoszulRegularImmersion
      (pieceImmersion ι g d O hOd) :=
  have := isClosedImmersion_pieceImmersion ι g d O hOd hOc
  isKoszulRegularImmersion_of_koszul f.left
    ((pieceOpen g d O).ι ≫ (dimensionOpen g d).ι ≫ g) (ι ⁻¹ᵁ O) (pieceImmersion ι g d O hOd)
    hlci (pieceImmersion_fac f ι g hfac d O hOd).symm

include hOc in
omit [AlgebraicGeometry.IsNoetherian S] [IsProper g] in
/-- The conormal sheaf of `ι⁻¹(O) ⟶ O` has rank `m` when the conormal sheaf of `ι` has fibre
rank `m` along `ι⁻¹(O)`. -/
theorem isFiniteLocallyFreeOfRank_pieceImmersion
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.left.ringCatSheaf) (Stacks.Conormal.conormalSheaf ι)] (m : ℕ)
    (hm : ∀ x ∈ ι ⁻¹ᵁ O, Scheme.Modules.fiberRank (Stacks.Conormal.conormalSheaf ι) x = m) :
    haveI := isClosedImmersion_pieceImmersion ι g d O hOd hOc
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := (ι ⁻¹ᵁ O).toScheme.ringCatSheaf)
      (Stacks.Conormal.conormalSheaf (pieceImmersion ι g d O hOd)) m :=
  have := isClosedImmersion_pieceImmersion ι g d O hOd hOc
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (conormalSheafRestrictIsoOfFac ι O (Scheme.Opens.isoOfLE hOd).hom
      (pieceImmersion ι g d O hOd) (pieceImmersion_comp_isoOfLE_hom ι g d O hOd))
    (Scheme.Modules.isFiniteLocallyFreeOfRank_restrict_of_fiberRank_eq
      (Stacks.Conormal.conormalSheaf ι) (ι ⁻¹ᵁ O) m hm)

include hfac hOd hOc in
/-- Let `O ⊆ P` be an open inside the coborder of `ι` and the locus of relative dimension `d` of
`g`, along whose preimage the conormal sheaf of `ι` has fibre rank `m`. Along `ι⁻¹(O)`, the
cohomology sheaf `H^k(f^!𝒪_Y)` has nonzero stalks exactly for `k = -(d - m)`, and there is a map
`(∧^{d-m} Ω_{X/Y})|_{ι⁻¹(O)} ⟶ H^{-(d-m)}(f^!𝒪_Y)|_{ι⁻¹(O)}` whose stalk at `x` is an isomorphism
exactly when `f` is smooth at `x`. -/
theorem upperShriekHomology_piece (hlci : IsLocalCompleteIntersectionMorphism f.left)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.left.ringCatSheaf) (Stacks.Conormal.conormalSheaf ι)] (m : ℕ)
    (hm : ∀ x ∈ ι ⁻¹ᵁ O, Scheme.Modules.fiberRank (Stacks.Conormal.conormalSheaf ι) x = m)
    (c : CompactificationOf (Over.mk f.left)) :
    (∀ x ∈ ι ⁻¹ᵁ O, ∀ k : ℤ,
      Nontrivial ↑((upperShriekHomology f c k).presheaf.stalk x) ↔ k = -((d : ℤ) - m)) ∧
    ∃ ψ : (Scheme.Modules.restrictFunctor (ι ⁻¹ᵁ O).ι).obj
        (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f.left) ((d : ℤ) - m)) ⟶
      (Scheme.Modules.restrictFunctor (ι ⁻¹ᵁ O).ι).obj
        (upperShriekHomology f c (-((d : ℤ) - m))),
      ∀ x : (ι ⁻¹ᵁ O).toScheme, IsIso (AlgebraicGeometry.SheafOfModules.stalkMap
          (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology
            ↥(ι ⁻¹ᵁ O).toScheme.toLocallyRingedSpace.toRingedSpace.carrier)
            (ι ⁻¹ᵁ O).toScheme.toLocallyRingedSpace.toRingedSpace.sheaf) x ψ) ↔
        InfinitesimalLifting.SmoothAt f.left ((ι ⁻¹ᵁ O).ι x) := by
  let i : (pieceFTS ι O).left ⟶ (pieceOpen g d O).toScheme := pieceImmersion ι g d O hOd
  have : IsClosedImmersion i := isClosedImmersion_pieceImmersion ι g d O hOd hOc
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (R := (pieceFTS ι O).left.ringCatSheaf) (Stacks.Conormal.conormalSheaf i) m :=
    isFiniteLocallyFreeOfRank_pieceImmersion ι g d O hOd hOc m hm
  have hi : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsKoszulRegularImmersion i :=
    isKoszulRegularImmersion_pieceImmersion f ι g hfac d O hOd hOc hlci
  have hf : i ≫ (pieceOpen g d O).ι ≫ (dimensionOpen g d).ι ≫ g = (pieceHom ι O ≫ f).left :=
    pieceImmersion_fac f ι g hfac d O hOd
  exact ⟨fun x hx k ↦
      (nontrivial_stalk_upperShriekHomology_comp_iff (pieceHom ι O) f c k ⟨x, hx⟩).symm.trans
        (nontrivial_stalk_upperShriekHomology_iff _ _ i _ hf _ d m hi ⟨x, hx⟩ k),
    exists_restrict_map_isIso_stalkMap_iff (pieceHom ι O) f c _
      (fundamentalClass _ _ i _ hf _ d m hi)
      (isIso_stalkMap_fundamentalClass_iff _ _ i _ hf _ d m hi)⟩

end Piece

section Global

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  {P : Scheme.{u}} (ι : X.left ⟶ P) [IsImmersion ι] (g : P ⟶ Y.left) [Smooth g] [IsProper g]
  (hfac : ι ≫ g = f.left)

include hfac in
omit [AlgebraicGeometry.IsNoetherian S] [IsProper g] in
/-- The conormal sheaf of the immersion `ι` is finite locally free. -/
theorem isFiniteLocallyFree_conormalSheaf (hlci : IsLocalCompleteIntersectionMorphism f.left) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.left.ringCatSheaf) (Stacks.Conormal.conormalSheaf ι) :=
  AlgebraicGeometry.RegularIdealSheaf.isFiniteLocallyFree_conormalSheaf_of_isH1RegularImmersion
    ι (Stacks.AlgebraicGeometry.RegularIdealSheaf.isH1RegularImmersion_of_isKoszulRegularImmersion
      ι (isKoszulRegularImmersion_of_koszul_comp_smooth ι g (hfac ▸ hlci)))

include hfac in
/-- Let `S` be Noetherian and `f : X ⟶ Y` a local complete intersection morphism of `FTS S`
which factors as an immersion `ι : X ⟶ P` followed by a proper smooth morphism `g : P ⟶ Y`; let
`f^!` be computed at any compactification `j` of `f`. Then there is a locally constant function
`r` on `X` such that `ω_{X/Y} = H^{-r}(f^!𝒪_Y)` is the only nonzero cohomology sheaf of `f^!𝒪_Y`
(the stalk of `H^k(f^!𝒪_Y)` at `x` is nonzero exactly for `k = -r(x)`), and a map
`∧^r Ω_{X/Y} ⟶ ω_{X/Y}` whose stalk at `x` is an isomorphism exactly when `f` is smooth at `x`.

As `r` is only locally constant, the map is given on each piece of a decomposition of `X` into
pairwise disjoint open and closed subschemes covering `X` on which `r` is constant. -/
@[stacks 0E9Z]
theorem exists_fundamentalClass_of_isLocalCompleteIntersection
    (hlci : IsLocalCompleteIntersectionMorphism f.left) (j : CompactificationOf (Over.mk f.left)) :
    ∃ r : X.left → ℤ, IsLocallyConstant r ∧
      (∀ (x : X.left) (k : ℤ),
        Nontrivial ↑((upperShriekHomology f j k).presheaf.stalk x) ↔ k = -r x) ∧
      ∃ (A : Type) (V : A → X.left.Opens) (n : A → ℤ),
        (∀ a, IsClosed (V a : Set X.left)) ∧ Pairwise (Function.onFun Disjoint V) ∧ (⨆ a, V a) = ⊤ ∧
        (∀ a, ∀ x ∈ V a, r x = n a) ∧
        ∀ a, ∃ φ : (Scheme.Modules.restrictFunctor (V a).ι).obj
            (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials f.left) (n a)) ⟶
          (Scheme.Modules.restrictFunctor (V a).ι).obj (upperShriekHomology f j (-n a)),
          ∀ x : (V a).toScheme, IsIso (AlgebraicGeometry.SheafOfModules.stalkMap
              (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology
                ↥(V a).toScheme.toLocallyRingedSpace.toRingedSpace.carrier)
                (V a).toScheme.toLocallyRingedSpace.toRingedSpace.sheaf) x φ) ↔
            InfinitesimalLifting.SmoothAt f.left ((V a).ι x) := by
  have := isFiniteLocallyFree_conormalSheaf f ι g hfac hlci
  let C : X.left.Modules := Stacks.Conormal.conormalSheaf ι
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.left.ringCatSheaf) C :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.toFiniteLocallyFree C ‹_›
  let mf : X.left → ℕ := Scheme.Modules.fiberRank C
  have hmf : IsLocallyConstant mf := Scheme.Modules.isLocallyConstant_fiberRank C
  let df : LocallyConstant P ℕ := relativeDimensionFunction g (isCohenMacaulay_fiber_of_smooth g)
  have hdf : IsLocallyConstant (fun x : X.left ↦ df (ι x)) :=
    df.isLocallyConstant.comp_continuous ι.continuous
  have hT : ∀ m : ℕ, ∃ T : P.Opens, ∀ x : X.left, x ∈ ι ⁻¹ᵁ T ↔ mf x = m := by
    intro m
    obtain ⟨t, ht, hts⟩ := ι.isEmbedding.isInducing.isOpen_iff.1 (hmf.isOpen_fiber m)
    exact ⟨⟨t, ht⟩, fun x ↦ Set.ext_iff.1 hts x⟩
  choose T hT using hT
  let O : ℕ × ℕ → P.Opens := fun a ↦ T a.2 ⊓ dimensionOpen g a.1 ⊓ ι.coborderRange
  have hmem : ∀ a x, x ∈ ι ⁻¹ᵁ O a ↔ mf x = a.2 ∧ df (ι x) = a.1 := by
    intro a x
    change (ι x ∈ T a.2 ∧ ι x ∈ dimensionOpen g a.1) ∧ ι x ∈ ι.coborderRange ↔ _
    have h3 := mem_relativeDimensionOpen g (isCohenMacaulay_fiber_of_smooth g) a.1 (ι x)
    exact ⟨fun h ↦ ⟨(hT a.2 x).1 h.1.1, h3.1 h.1.2⟩,
      fun h ↦ ⟨⟨(hT a.2 x).2 h.1, h3.2 h.2⟩, subset_coborder ⟨x, rfl⟩⟩⟩
  have hself : ∀ x, x ∈ ι ⁻¹ᵁ O (df (ι x), mf x) := fun x ↦ (hmem _ x).2 ⟨rfl, rfl⟩
  have piece := fun a : ℕ × ℕ ↦ upperShriekHomology_piece f ι g hfac a.1 (O a)
    (inf_le_left.trans inf_le_right) inf_le_right hlci a.2 (fun x hx ↦ ((hmem a x).1 hx).1) j
  refine ⟨fun x ↦ (df (ι x) : ℤ) - mf x, IsLocallyConstant.comp₂ hdf hmf fun a b ↦ (a : ℤ) - b,
    fun x k ↦ (piece (df (ι x), mf x)).1 x (hself x) k,
    ℕ × ℕ, fun a ↦ ι ⁻¹ᵁ O a, fun a ↦ (a.1 : ℤ) - a.2, fun a ↦ ?_, fun a b hab ↦ ?_, ?_,
    fun a x hx ↦ ?_, fun a ↦ (piece a).2⟩
  · have hV : ((ι ⁻¹ᵁ O a : X.left.Opens) : Set X.left) =
        {x | mf x = a.2} ∩ {x | df (ι x) = a.1} := Set.ext fun x ↦ hmem a x
    rw [hV]
    exact (hmf.isClosed_fiber _).inter (hdf.isClosed_fiber _)
  · refine TopologicalSpace.Opens.coe_disjoint.mp (Set.disjoint_left.2 fun x hxa hxb ↦ hab ?_)
    obtain ⟨h1, h2⟩ := (hmem a x).1 hxa
    obtain ⟨h3, h4⟩ := (hmem b x).1 hxb
    exact Prod.ext (h2.symm.trans h4) (h1.symm.trans h3)
  · exact eq_top_iff.2 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2
      ⟨(df (ι x), mf x), hself x⟩
  · obtain ⟨h1, h2⟩ := (hmem a x).1 hx
    exact congrArg₂ (fun a b : ℕ ↦ (a : ℤ) - b) h2 h1

end Global

end Stacks.Duality.ClosedOpenProperFactorization
