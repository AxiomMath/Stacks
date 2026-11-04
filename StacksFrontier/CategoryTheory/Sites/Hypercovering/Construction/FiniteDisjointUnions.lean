module

public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits
public import StacksFrontier.CategoryTheory.Sites.CoveringPermanence
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.DisjointUnions

/-!
# Taking finite disjoint unions in a hypercovering

The disjoint-union construction of Stacks 0DB2 is carried out here on the semi-representable
objects with *finitely many* summands instead of on all those whose coproduct happens to exist.

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.indices` is the index type of a formal coproduct, as a
  functor to types.
* `Stacks.CategoryTheory.Hypercovering.FiniteFormalCoproduct` is the full subcategory of formal
  coproducts with a finite index type.
* `Stacks.CategoryTheory.Hypercovering.takeUnionsFin` takes the coproduct of such a family and
  regards it as a singleton formal coproduct.

## Main results

* `Stacks.CategoryTheory.Hypercovering.isClosedUnderFiniteLimits_finite_I`: finitely indexed
  formal coproducts are closed under finite limits.
* `Stacks.CategoryTheory.Hypercovering.isPullback_sigmaMap'`: the van Kampen decomposition of a
  fibre product of two finite disjoint unions over a third.
* `PreservesFiniteLimits (takeUnionsFin (C := C))`: taking finite disjoint unions commutes with
  finite limits, which with the closure statement above is what the construction of Stacks 09A1
  needs of Stacks 0DB2.

## Implementation notes

The point of working with the finite families rather than with the summable ones is that the two
hypotheses of Stacks 0DB2 which quantify over *all* families with a coproduct — closure under
finite limits, and preservation of finite limits by taking the coproduct — hold for the finite
families in any category with finite coproducts and fibre products in which finite coproducts are
van Kampen, whereas for the summable families they fail as soon as the ambient category is not
cocomplete: there the categorical coproduct of an infinite family need not be its disjoint union.
The construction of Stacks 09A1 only ever takes disjoint unions of the degreewise finite
hypercovering produced by Stacks 094K, so nothing is lost.

Closure under finite limits is read off from `indices`: the index type of a formal coproduct is a
functor to types which preserves the terminal object (a one-point index type) and fibre products
(the index type of a fibre product is `Function.Pullback` of the index maps), hence all finite
limits; a finite limit of finite types is finite.

Preservation of finite limits by `takeUnionsFin` is the van Kampen property of finite coproducts:
the fibre product of `∐ Aᵢ` and `∐ Bⱼ` over `∐ Zₖ` decomposes as the coproduct, over the pairs
`(i, j)` with the same image index, of `Aᵢ ×_{Zₖ} Bⱼ`, the mismatched pairs contributing an
initial object because a coproduct in an extensive category is disjoint.

## References

* [Stacks Project, Tag 0DB2](https://stacks.math.columbia.edu/tag/0DB2)
* [Stacks Project, Tag 09A1](https://stacks.math.columbia.edu/tag/09A1)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C]

/-! ### Finitely indexed formal coproducts are closed under finite limits -/

/-- The index type of a formal coproduct, as a functor to types. -/
@[simps]
def indices : FormalCoproduct.{w} C ⥤ Type w where
  obj U := U.I
  map f := TypeCat.ofHom f.f

/-- The index-type functor `indices` preserves the terminal object. -/
instance [HasTerminal C] :
    PreservesLimit (Functor.empty.{0} (FormalCoproduct.{w} C)) (indices.{w} (C := C)) :=
  preservesLimit_of_preserves_limit_cone
    (FormalCoproduct.isTerminalIncl (⊤_ C) terminalIsTerminal)
    ((isLimitMapConeEmptyConeEquiv _ _).symm Types.isTerminalPUnit)

/-- The index-type functor `indices` preserves limits of the empty diagram. -/
instance [HasTerminal C] :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (indices.{w} (C := C)) :=
  preservesLimitsOfShape_pempty_of_preservesTerminal _

/-- The index-type functor `indices` preserves fibre products: the index type of a fibre product
is `Function.Pullback` of the index maps. -/
instance [HasPullbacks C] :
    PreservesLimitsOfShape WalkingCospan (indices.{w} (C := C)) := by
  apply Limits.preservesLimitsOfShape_walkingCospan_of_forall_isPullback
  intro A B Z f g _
  refine ⟨_, pullbackFormalCoproduct.fst f g (pullbackConeFamily f g),
    pullbackFormalCoproduct.snd f g (pullbackConeFamily f g),
    IsPullback.of_isLimit (pullbackFormalCoproduct.isLimit f g (pullbackConeFamily f g)
      (fun _ ↦ pullback.isLimit _ _)), ?_⟩
  rw [Types.isPullback_iff]
  refine ⟨?_, fun p q h ↦ Subtype.ext (Prod.ext h.1 h.2), fun i j h ↦ ⟨⟨(i, j), h⟩, rfl, rfl⟩⟩
  ext p
  exact p.2

/-- The index-type functor `indices` preserves finite limits. -/
instance [HasTerminal C] [HasPullbacks C] : PreservesFiniteLimits (indices.{w} (C := C)) :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

/-- A finite limit of formal coproducts with finitely many summands again has finitely many
summands: the index type of a limit is the limit of the index types. -/
instance isClosedUnderFiniteLimits_finite_I [HasTerminal C] [HasPullbacks C] :
    ObjectProperty.IsClosedUnderFiniteLimits
      (fun U : FormalCoproduct.{w} C ↦ Finite U.I) where
  isClosedUnderLimitsOfShape J _ _ := by
    constructor
    rintro A ⟨h⟩
    have hobj : ∀ j : J, Finite ((h.diag ⋙ indices.{w} (C := C)).obj j) := h.prop_diag_obj
    exact Finite.of_equiv _ (Limits.Types.isLimitEquivSections
      (isLimitOfPreserves (indices.{w} (C := C)) h.isLimit)).symm

/-! ### The category of finitely indexed formal coproducts -/

variable (C) in
/-- Formal coproducts with a finite index type. -/
abbrev FiniteFormalCoproduct :=
  ObjectProperty.FullSubcategory (fun U : FormalCoproduct.{w} C ↦ Finite U.I)

/-- A finitely indexed formal coproduct has a coproduct as soon as the ambient category has
finite coproducts. -/
lemma hasCoproduct_of_finite_I [HasFiniteCoproducts C] (U : FormalCoproduct.{w} C)
    (hU : Finite U.I) : HasCoproduct U.obj :=
  have := hU
  inferInstance

/-- The inclusion of the finitely indexed formal coproducts into the summable ones. -/
abbrev finiteInclusion [HasFiniteCoproducts C] :
    FiniteFormalCoproduct.{w} C ⥤ SummableFormalCoproduct.{w} C :=
  ObjectProperty.ιOfLE hasCoproduct_of_finite_I

/-- Take a finitely indexed formal coproduct and regard its coproduct as a singleton formal
coproduct. -/
noncomputable def takeUnionsFin [HasFiniteCoproducts C] :
    FiniteFormalCoproduct.{w} C ⥤ FormalCoproduct.{w} C :=
  finiteInclusion (C := C) ⋙ takeUnions (C := C)

/-! ### The one-summand embedding preserves finite limits -/

/-- Two equal morphisms into a one-summand semi-representable object have equal components. -/
lemma φ_eq_of_eq {T : FormalCoproduct.{w} C} {X : C}
    {a b : T ⟶ (FormalCoproduct.incl.{w} C).obj X} (h : a = b) (i : T.I) :
    (a.φ i : T.obj i ⟶ X) = b.φ i := by
  subst h
  rfl

/-- The fibre product of two one-summand semi-representable objects is the one-summand object on
the fibre product in the ambient category. -/
lemma isPullback_map_incl [HasPullbacks C] {X Y Z : C} (x : X ⟶ Z) (y : Y ⟶ Z) :
    IsPullback ((FormalCoproduct.incl.{w} C).map (pullback.fst x y))
      ((FormalCoproduct.incl.{w} C).map (pullback.snd x y))
      ((FormalCoproduct.incl.{w} C).map x) ((FormalCoproduct.incl.{w} C).map y) := by
  have hcomm : (FormalCoproduct.incl.{w} C).map (pullback.fst x y) ≫
        (FormalCoproduct.incl.{w} C).map x =
      (FormalCoproduct.incl.{w} C).map (pullback.snd x y) ≫
        (FormalCoproduct.incl.{w} C).map y := by
    rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]
  have hcond : ∀ (s : PullbackCone ((FormalCoproduct.incl.{w} C).map x)
      ((FormalCoproduct.incl.{w} C).map y)) (i : s.pt.I),
      s.fst.φ i ≫ x = s.snd.φ i ≫ y := fun s i ↦ φ_eq_of_eq s.condition i
  refine IsPullback.of_isLimit' ⟨hcomm⟩ (PullbackCone.IsLimit.mk hcomm
    (fun s ↦ ⟨fun _ ↦ PUnit.unit, fun i ↦ pullback.lift (s.fst.φ i) (s.snd.φ i) (hcond s i)⟩)
    (fun s ↦ ?_) (fun s ↦ ?_) (fun s m h₁ h₂ ↦ ?_))
  · exact FormalCoproduct.hom_ext_heq (funext fun i ↦ rfl)
      (heq_of_eq (funext fun i ↦ pullback.lift_fst _ _ (hcond s i)))
  · exact FormalCoproduct.hom_ext_heq (funext fun i ↦ rfl)
      (heq_of_eq (funext fun i ↦ pullback.lift_snd _ _ (hcond s i)))
  · have key : ∀ i : s.pt.I, (m.φ i : s.pt.obj i ⟶ pullback x y) =
        pullback.lift (s.fst.φ i) (s.snd.φ i) (hcond s i) := fun i ↦
      pullback.hom_ext ((φ_eq_of_eq h₁ i).trans (pullback.lift_fst _ _ (hcond s i)).symm)
        ((φ_eq_of_eq h₂ i).trans (pullback.lift_snd _ _ (hcond s i)).symm)
    exact FormalCoproduct.hom_ext_heq (funext fun i ↦ rfl) (heq_of_eq (funext key))

/-- The one-summand embedding `FormalCoproduct.incl` preserves fibre products. -/
instance [HasPullbacks C] :
    PreservesLimitsOfShape WalkingCospan (FormalCoproduct.incl.{w} C) :=
  Limits.preservesLimitsOfShape_walkingCospan_of_forall_isPullback fun _ _ _ x y _ ↦
    ⟨_, pullback.fst x y, pullback.snd x y, IsPullback.of_hasPullback x y, isPullback_map_incl x y⟩

/-- The one-summand embedding `FormalCoproduct.incl` preserves finite limits. -/
instance [HasTerminal C] [HasPullbacks C] :
    PreservesFiniteLimits (FormalCoproduct.incl.{w} C) := by
  have : PreservesLimit (Functor.empty.{0} C) (FormalCoproduct.incl.{w} C) :=
    preservesTerminal_of_iso _
      ((FormalCoproduct.isTerminalIncl (⊤_ C) terminalIsTerminal).uniqueUpToIso terminalIsTerminal)
  have := preservesLimitsOfShape_pempty_of_preservesTerminal (FormalCoproduct.incl.{w} C)
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

/-- A one-summand formal coproduct has a finite index type. -/
instance finite_I_incl (X : C) : Finite ((FormalCoproduct.incl.{w} C).obj X).I :=
  inferInstanceAs (Finite PUnit.{w + 1})

/-! ### Taking finite disjoint unions preserves finite limits -/

/-- A cofan whose summands outside a subtype are initial is a colimit as soon as the coproduct
over that subtype is: the initial summands contribute nothing. -/
noncomputable def isColimitCofanOfSubtype [HasInitial C] {ι : Type*} (Q : ι → C) (S : ι → Prop)
    [DecidablePred S] (R : {i // S i} → C) [HasCoproduct R]
    (e : ∀ i : {i // S i}, Q i.1 ≅ R i) (hS : ∀ i, ¬ S i → IsInitial (Q i)) :
    IsColimit (Cofan.mk (∐ R) (fun i ↦ if h : S i then (e ⟨i, h⟩).hom ≫ Sigma.ι R ⟨i, h⟩
      else (hS i h).to _)) := by
  refine Cofan.IsColimit.mk _ (fun t ↦ Sigma.desc (fun i ↦ (e i).inv ≫ t.inj i.1))
    (fun t i ↦ ?_) (fun t m hm ↦ ?_)
  · by_cases h : S i
    · simp only [cofan_mk_inj, dif_pos h, Category.assoc, Sigma.ι_desc,
        Iso.hom_inv_id_assoc]
    · simp only [cofan_mk_inj, dif_neg h]
      exact (hS i h).hom_ext _ _
  · refine Sigma.hom_ext (f := R) _ _ (fun i ↦ ?_)
    have h := hm i.1
    simp only [cofan_mk_inj, dif_pos i.2, Category.assoc] at h
    simp [← h]

variable [HasPullbacks C] [FinitaryExtensive C]

/-- A pair of indices with the same image contributes the componentwise fibre product. -/
private lemma isPullback_pullbackConeFamily_comp_ι {A B Z : FormalCoproduct.{w} C} (f : A ⟶ Z)
    (g : B ⟶ Z) [Finite Z.I] (p : Function.Pullback f.f g.f) :
    IsPullback (pullbackConeFamily f g p).fst (pullbackConeFamily f g p).snd
      (f.φ p.1.1 ≫ Sigma.ι Z.obj (f.f p.1.1)) (g.φ p.1.2 ≫ Sigma.ι Z.obj (g.f p.1.2)) := by
  have hvk : IsVanKampenColimit (Cofan.mk (∐ Z.obj) (Sigma.ι Z.obj)) :=
    FinitaryExtensive.isVanKampen_finiteCoproducts (coproductIsCoproduct Z.obj)
  have hι : ∀ (k l : Z.I) (h : k = l),
      eqToHom (congrArg Z.obj h) ≫ Sigma.ι Z.obj l = Sigma.ι Z.obj k := by
    intro k l h
    subst h
    simp
  have hm : Mono (Sigma.ι Z.obj (g.f p.1.2)) := mono_of_cofan_isVanKampen hvk ⟨g.f p.1.2⟩
  have ht : IsPullback (g.φ p.1.2) (𝟙 (B.obj p.1.2)) (Sigma.ι Z.obj (g.f p.1.2))
      (g.φ p.1.2 ≫ Sigma.ι Z.obj (g.f p.1.2)) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have h := (IsPullback.of_hasPullback
    (f.φ p.1.1 ≫ eqToHom (congrArg Z.obj p.2)) (g.φ p.1.2)).paste_vert ht
  rw [Category.assoc, hι _ _ p.2] at h
  simpa using h

/-- A pair of indices with different images contributes an initial object. -/
private noncomputable def isInitialPullbackCompιOfNe {A B Z : FormalCoproduct.{w} C} (f : A ⟶ Z)
    (g : B ⟶ Z) [Finite Z.I] (q : A.I × B.I) (hq : ¬ (f.f q.1 = g.f q.2)) :
    IsInitial (pullback (f.φ q.1 ≫ Sigma.ι Z.obj (f.f q.1))
      (g.φ q.2 ≫ Sigma.ι Z.obj (g.f q.2))) := by
  have hvk : IsVanKampenColimit (Cofan.mk (∐ Z.obj) (Sigma.ι Z.obj)) :=
    FinitaryExtensive.isVanKampen_finiteCoproducts (coproductIsCoproduct Z.obj)
  have hd : IsPullback (initial.to (Z.obj (f.f q.1))) (initial.to (Z.obj (g.f q.2)))
      (Sigma.ι Z.obj (f.f q.1)) (Sigma.ι Z.obj (g.f q.2)) := by
    simpa using isPullback_initial_to_of_cofan_isVanKampen hvk ⟨f.f q.1⟩ ⟨g.f q.2⟩
      (by simpa using hq)
  have hcomm : (pullback.fst (f.φ q.1 ≫ Sigma.ι Z.obj (f.f q.1))
        (g.φ q.2 ≫ Sigma.ι Z.obj (g.f q.2)) ≫ f.φ q.1) ≫ Sigma.ι Z.obj (f.f q.1) =
      (pullback.snd (f.φ q.1 ≫ Sigma.ι Z.obj (f.f q.1))
        (g.φ q.2 ≫ Sigma.ι Z.obj (g.f q.2)) ≫ g.φ q.2) ≫ Sigma.ι Z.obj (g.f q.2) := by
    simpa only [Category.assoc] using pullback.condition
      (f := f.φ q.1 ≫ Sigma.ι Z.obj (f.f q.1)) (g := g.φ q.2 ≫ Sigma.ι Z.obj (g.f q.2))
  have := HasStrictInitialObjects.out (hd.lift _ _ hcomm) initialIsInitial
  exact IsInitial.ofIso initialIsInitial (asIso (hd.lift _ _ hcomm)).symm

/-- **The van Kampen decomposition of a fibre product of finite disjoint unions.** The fibre
product of `∐ Aᵢ` and `∐ Bⱼ` over `∐ Zₖ` is the coproduct, over the pairs of indices with the
same image, of the componentwise fibre products. -/
lemma isPullback_sigmaMap' {A B Z : FormalCoproduct.{w} C} (f : A ⟶ Z) (g : B ⟶ Z)
    [Finite A.I] [Finite B.I] [Finite Z.I] :
    IsPullback
      (Sigma.map' (fun p : Function.Pullback f.f g.f ↦ p.1.1)
        (fun p ↦ (pullbackConeFamily f g p).fst))
      (Sigma.map' (fun p : Function.Pullback f.f g.f ↦ p.1.2)
        (fun p ↦ (pullbackConeFamily f g p).snd))
      (Sigma.map' f.f f.φ) (Sigma.map' g.f g.φ) := by
  classical
  have hau : IsUniversalColimit (Cofan.mk (∐ A.obj) (Sigma.ι A.obj)) :=
    FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct A.obj)
  have hbu : IsUniversalColimit (Cofan.mk (∐ B.obj) (Sigma.ι B.obj)) :=
    FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct B.obj)
  have hu : ∀ i, Sigma.ι A.obj i ≫ Sigma.map' f.f f.φ = f.φ i ≫ Sigma.ι Z.obj (f.f i) :=
    Sigma.ι_comp_map' _ _
  have hv : ∀ j, Sigma.ι B.obj j ≫ Sigma.map' g.f g.φ = g.φ j ≫ Sigma.ι Z.obj (g.f j) :=
    Sigma.ι_comp_map' _ _
  have hinit := isInitialPullbackCompιOfNe f g
  have hd := isColimitCofanOfSubtype
    (fun q : A.I × B.I ↦ pullback (f.φ q.1 ≫ Sigma.ι Z.obj (f.f q.1))
      (g.φ q.2 ≫ Sigma.ι Z.obj (g.f q.2)))
    (fun q ↦ f.f q.1 = g.f q.2) (fun p ↦ (pullbackConeFamily f g p).pt)
    (fun p ↦ (isPullback_pullbackConeFamily_comp_ι f g p).isoPullback.symm) hinit
  have hmain := hau.isPullback_prod_of_isColimit hbu
    (fun i ↦ f.φ i ≫ Sigma.ι Z.obj (f.f i)) (fun j ↦ g.φ j ≫ Sigma.ι Z.obj (g.f j))
    (Sigma.map' f.f f.φ) (Sigma.map' g.f g.φ)
    (fun i j ↦ IsPullback.of_hasPullback _ _) _ hd hu hv
  convert hmain using 1
  any_goals rfl
  all_goals
    refine Cofan.IsColimit.hom_ext hd _ _ (fun q ↦ ?_)
    rw [Cofan.IsColimit.fac]
    by_cases h : f.f q.1 = g.f q.2
    · simp [h, IsPullback.isoPullback_inv_fst_assoc, IsPullback.isoPullback_inv_snd_assoc]
    · simp only [cofan_mk_inj, dif_neg h]
      exact (hinit q h).hom_ext _ _

variable [HasTerminal C] [HasFiniteCoproducts C]

/-- The one-element family on a terminal object is terminal among the finitely indexed formal
coproducts. -/
noncomputable def isTerminalInclTerminal :
    IsTerminal (⟨(FormalCoproduct.incl.{w} C).obj (⊤_ C), inferInstance⟩ :
      FiniteFormalCoproduct.{w} C) :=
  IsTerminal.ofUniqueHom (fun W ↦ ObjectProperty.homMk
    ((FormalCoproduct.isTerminalIncl (⊤_ C) terminalIsTerminal).from W.obj))
    (fun _ _ ↦ ObjectProperty.hom_ext (h :=
      (FormalCoproduct.isTerminalIncl (⊤_ C) terminalIsTerminal).hom_ext _ _))

/-- Taking finite disjoint unions preserves the terminal object. -/
instance :
    PreservesLimit (Functor.empty.{0} (FiniteFormalCoproduct.{w} C))
      (takeUnionsFin.{w} (C := C)) := by
  refine preservesLimit_of_preserves_limit_cone isTerminalInclTerminal
    ((isLimitMapConeEmptyConeEquiv _ _).symm (FormalCoproduct.isTerminalIncl _ ?_))
  exact IsTerminal.ofIso terminalIsTerminal (coproductUniqueIso (fun _ : PUnit.{w + 1} ↦ ⊤_ C)).symm

/-- Taking finite disjoint unions preserves limits of the empty diagram. -/
instance :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (takeUnionsFin.{w} (C := C)) :=
  preservesLimitsOfShape_pempty_of_preservesTerminal _

/-- Taking finite disjoint unions preserves fibre products. -/
instance : PreservesLimitsOfShape WalkingCospan (takeUnionsFin.{w} (C := C)) := by
  apply Limits.preservesLimitsOfShape_walkingCospan_of_forall_isPullback
  intro A B Z f g _
  have hA : Finite A.obj.I := A.property
  have hB : Finite B.obj.I := B.property
  have hZ : Finite Z.obj.I := Z.property
  refine ⟨⟨pullbackFormalCoproduct f.hom g.hom (pullbackConeFamily f.hom g.hom),
      inferInstanceAs (Finite (Function.Pullback f.hom.f g.hom.f))⟩,
    ObjectProperty.homMk (pullbackFormalCoproduct.fst f.hom g.hom
      (pullbackConeFamily f.hom g.hom)),
    ObjectProperty.homMk (pullbackFormalCoproduct.snd f.hom g.hom
      (pullbackConeFamily f.hom g.hom)), ?_, ?_⟩
  · exact IsPullback.of_map_of_faithful (ObjectProperty.ι _)
      (IsPullback.of_isLimit (pullbackFormalCoproduct.isLimit f.hom g.hom
        (pullbackConeFamily f.hom g.hom) (fun _ ↦ pullback.isLimit _ _)))
  · exact (isPullback_sigmaMap' f.hom g.hom).map (FormalCoproduct.incl.{w} C)

/-- **The second hypothesis of Stacks 0DB2 for finite disjoint unions.** In a category with fibre
products in which finite coproducts are van Kampen, taking the disjoint union of a finite family
commutes with finite limits. -/
instance : PreservesFiniteLimits (takeUnionsFin.{w} (C := C)) :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

end Stacks.CategoryTheory.Hypercovering

end
