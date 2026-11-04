module

public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.GlueingExistence
public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.CechCompatibility
import StacksCore.Tactic.StacksAttribute

/-!
# Glueing objects of the derived category along a covering

Let `(C, O_C)` be a ringed site with fibre products and `{U_i ⟶ X}_{i ∈ I}` a covering in `C`.
Let `E_i` be objects of `D(O_{U_i})` and `ρ_{ij} : E_i|_{U_{ij}} ⟶ E_j|_{U_{ij}}` isomorphisms on
the overlaps `U_{ij} = U_i ×_X U_j`, satisfying the cocycle condition on the triple overlaps,
such that the negative self-exts of the `E_i` vanish locally and the cohomology sheaves of the
`E_i` vanish uniformly to the left. Then there is a pair `(E, ρ_i)` of an object `E` of
`D(O_X)` and isomorphisms `ρ_i : E|_{U_i} ⟶ E_i` compatible with the `ρ_{ij}`, unique up to
unique isomorphism (Stacks 0GMG).

The proof follows the first proof of Stacks 0GMG. The data of Situation 0DC9 on `C/X` attached
to the covering are glued by Stacks 0DCA, along the Čech object `K` of the covering, to a cartesian
object of `D(O)` on the total site of `K`; it is bounded below, hence by Stacks 0D7S the
restriction `La^*M` of an object `M` of `D(O_X)`. Comparing the summandwise identification of
`La^*M` with the locally given objects with the canonical one of `La^*M` with the restrictions
of `M` gives, on the summands of degree `0`, the isomorphisms `ρ_i`, and on the summands of
degree `1`, their compatibility with the `ρ_{ij}`. Uniqueness is the uniqueness clause of Stacks
0DCA together with the full faithfulness of `La^*` (Stacks 0DA5).

## Main definitions

* `AlgebraicGeometry.RingedSite.CoveringGlueing.Glueing`: a pair `(E, ρ_i)`.

## Main results

* `AlgebraicGeometry.RingedSite.CoveringGlueing.existsUnique_glueing`: **Stacks 0GMG**.

## Implementation notes

The hypothesis `SheafExt^p_{O_{U_i}}(E_i, E_i) = 0` for `p < 0` is stated as the vanishing of the
negative self-exts of `E_i|_V` for every object `V` over `U_i`. For negative degrees the two
are equivalent, by the local-to-global spectral sequence of `RHom(E_i, E_i)`, and the second is
the form in which the source's proof uses the hypothesis.

The derived categories are those of the sheaves of modules on the slices, in the universe of the
site, as in Situation 0DC9 (`AlgebraicGeometry.RingedSite.LocalDerivedCategory`).

## References

* [Stacks Project, Tag 0GMG](https://stacks.math.columbia.edu/tag/0GMG)
* [Stacks Project, Tag 0DCA](https://stacks.math.columbia.edu/tag/0DCA)
* [Stacks Project, Tag 0DA5](https://stacks.math.columbia.edu/tag/0DA5)
* [Stacks Project, Tag 0D7S](https://stacks.math.columbia.edu/tag/0D7S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Simplicial

universe u

namespace CategoryTheory

/-- Composites become equal once they do after two functors, the second faithful and the first
injective on the morphisms at hand. -/
theorem comp_eq_of_map_comp_eq {𝒜 𝒜' 𝒟 : Type*} [Category 𝒜] [Category 𝒜'] [Category 𝒟]
    (F : 𝒜 ⥤ 𝒜') (T : 𝒜' ⥤ 𝒟) [T.Faithful] {a b c : 𝒜}
    (hF : ∀ x y : a ⟶ c, F.map x = F.map y → x = y) (x : a ⟶ b) (y : b ⟶ c) (z : a ⟶ c)
    (h : T.map (F.map x) ≫ T.map (F.map y) = T.map (F.map z)) : x ≫ y = z := by
  apply hF
  apply T.map_injective
  rw [F.map_comp, T.map_comp, h]

/-- Equal composites have equal images under two functors. -/
theorem map_comp_eq_of_comp_eq {𝒜 𝒜' 𝒟 : Type*} [Category 𝒜] [Category 𝒜'] [Category 𝒟]
    (F : 𝒜 ⥤ 𝒜') (T : 𝒜' ⥤ 𝒟) {a b c : 𝒜} (x : a ⟶ b) (y : b ⟶ c) (z : a ⟶ c)
    (h : x ≫ y = z) : T.map (F.map x) ≫ T.map (F.map y) = T.map (F.map z) := by
  rw [← T.map_comp, ← F.map_comp, h]

/-- The diagram chase translating a compatibility through a natural isomorphism. -/
theorem comp_iff_of_naturality {𝒞 : Type*} [Category 𝒞] {a b c d z : 𝒞} (x : a ⟶ b) (k : a ≅ c)
    (k' : b ⟶ d) (y : c ⟶ d) (θA : c ⟶ z) (θB : d ⟶ z) (nat : x ≫ k' = k.hom ≫ y) :
    x ≫ k' ≫ θB = k.hom ≫ θA ↔ y ≫ θB = θA := by
  rw [← Category.assoc, nat, Category.assoc, cancel_epi]

end CategoryTheory

namespace AlgebraicGeometry.RingedSite.CoveringGlueing

open CategoryTheory.SimplicialSemiRepresentable

attribute [local instance] HasDerivedCategory.standard

section Glueing

variable {X : RingedSite.{u, u, u}} [HasPullbacks X.C] {X₀ : X.C} {ι : Type u} {U : ι → X.C}
  (f : ∀ i, U i ⟶ X₀) (E : ∀ i, LocalDerivedCategory.{0} X (U i))
  (ρ : ∀ i j, (derivedOverMap.{0} X (pullback.fst (f i) (f j))).obj (E i) ≅
    (derivedOverMap.{0} X (pullback.snd (f i) (f j))).obj (E j))

/-- **A pair `(E, ρ_i)` as in Stacks 0GMG**: an object of `D(O_X)` with isomorphisms
`ρ_i : E|_{U_i} ⟶ E_i` compatible with the `ρ_{ij}`, that is, `ρ_{ij}` composed with the
restriction of `ρ_i` to `U_{ij}` is the restriction of `ρ_j`, through the canonical
identification of the two restrictions of `E` to `U_{ij}`. -/
structure Glueing where
  /-- The global object. -/
  obj : LocalDerivedCategory.{0} X X₀
  /-- The identification of its restriction to `U_i` with `E_i`. -/
  iso : ∀ i, (derivedOverMap.{0} X (f i)).obj obj ≅ E i
  /-- The identifications are compatible with the `ρ_{ij}`. -/
  compatibility : ∀ i j,
    (derivedOverMap.{0} X (pullback.fst (f i) (f j))).map (iso i).hom ≫ (ρ i j).hom =
      (canonicalOverlap f obj i j).hom ≫
        (derivedOverMap.{0} X (pullback.snd (f i) (f j))).map (iso j).hom

end Glueing

attribute [local instance] pretopologyRingedSite_over_hasPullbacks

variable {C : Type u} [SmallCategory C] [HasPullbacks C] {P : Pretopology C} {X : C}
  {OC : Sheaf P.toGrothendieck CommRingCat.{u}} {ι : Type u} {U : ι → C} {f : ∀ i, U i ⟶ X}
  {E : ∀ i, LocalDerivedCategory.{0} (pretopologyRingedSite P OC) (U i)}
  {ρ : ∀ i j, (derivedOverMap.{0} (pretopologyRingedSite P OC) (pullback.fst (f i) (f j))).obj
      (E i) ≅ (derivedOverMap.{0} (pretopologyRingedSite P OC) (pullback.snd (f i) (f j))).obj
        (E j)}

/-- The isomorphisms of the locally given objects on the summands of the Čech object obtained by
comparing a summandwise identification of the restriction of a global object `M` with the
canonical one, read on the slices of `C`. -/
def summandComparison (hρ : IsCocycle (X := pretopologyRingedSite P OC) f ρ)
    (M : LocalDerivedCategory.{0} (pretopologyRingedSite P OC) X)
    (σ : (coveringLocallyGiven P OC f E ρ hρ).SummandIdentification
      (cechLift (X := pretopologyRingedSite P OC) f)
      ((cechTotalRestriction P OC f).mapDerivedCategory.obj M))
    (n : SimplexCategory) (t : ((cechLift (X := pretopologyRingedSite P OC) f).obj (op n)).I) :
    (derivedOverMap.{0} (pretopologyRingedSite P OC)
        (((cechLift (X := pretopologyRingedSite P OC) f).obj (op n)).obj t).a).obj
          ((derivedOverMap.{0} (pretopologyRingedSite P OC) (f (t 0))).obj M) ≅
      (derivedOverMap.{0} (pretopologyRingedSite P OC)
        (((cechLift (X := pretopologyRingedSite P OC) f).obj (op n)).obj t).a).obj (E (t 0)) :=
  haveI := RingedSite.derivedIteratedSliceTransport_isEquivalence (pretopologyRingedSite P OC) X
    (((cechLift (X := pretopologyRingedSite P OC) f).obj (op n)).obj t).V
  (Functor.FullyFaithful.ofFullyFaithful ((pretopologyRingedSite P OC).derivedIteratedSliceTransport
    X (((cechLift (X := pretopologyRingedSite P OC) f).obj (op n)).obj t).V)).preimageIso
      (((canonicalSummandIdentification P OC f M).iso n t).symm ≪≫ σ.iso n t)

/-- The comparison isomorphisms on the summands of the Čech object are compatible with the
isomorphisms `ρ_g` along the arrows of the Čech object. -/
theorem summandComparison_comm (hρ : IsCocycle (X := pretopologyRingedSite P OC) f ρ)
    (M : LocalDerivedCategory.{0} (pretopologyRingedSite P OC) X)
    (σ : (coveringLocallyGiven P OC f E ρ hρ).SummandIdentification
      (cechLift (X := pretopologyRingedSite P OC) f)
      ((cechTotalRestriction P OC f).mapDerivedCategory.obj M))
    {m n : SimplexCategory} (φ : m ⟶ n)
    (t : ((cechLift (X := pretopologyRingedSite P OC) f).obj (op n)).I) :
    (derivedOverMap.{0} (pretopologyRingedSite P OC)
        (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).φ t).hom.left).map
          (summandComparison hρ M σ m
            (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).f t)).hom ≫
        (indexRhoBase (X := pretopologyRingedSite P OC) f E ρ
          (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).φ t)).hom =
      (indexRhoBase (X := pretopologyRingedSite P OC) f
          (fun i => (derivedOverMap.{0} (pretopologyRingedSite P OC) (f i)).obj M)
          (canonicalOverlap (X := pretopologyRingedSite P OC) f M)
          (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).φ t)).hom ≫
        (summandComparison hρ M σ n t).hom := by
  have h := LocallyGiven.SummandIdentification.restriction_map_comp_rho
      (G := globalLocallyGiven P OC f M) (L := cechLift (X := pretopologyRingedSite P OC) f)
      (obj' := fun b => indexObj (X := pretopologyRingedSite P OC) f E
        (b : IndexCategory (X := pretopologyRingedSite P OC) f))
      (rho' := fun {b' b} g => indexRho (X := pretopologyRingedSite P OC) f E ρ
        (b := (b : IndexCategory (X := pretopologyRingedSite P OC) f))
        (b' := (b' : IndexCategory (X := pretopologyRingedSite P OC) f)) g)
      (cocycle' := (locallyGiven (X := pretopologyRingedSite P OC) f E ρ hρ).cocycle)
      (canonicalSummandIdentification P OC f M) σ φ t
  exact (indexRho_comm_iff_preimage (X := pretopologyRingedSite P OC) (E := E)
    (E' := fun i => (derivedOverMap.{0} (pretopologyRingedSite P OC) (f i)).obj M) f ρ
    (canonicalOverlap (X := pretopologyRingedSite P OC) f M)
    (((cechLift (X := pretopologyRingedSite P OC) f).map φ.op).φ t) _ _).1 h

variable (P OC f E ρ) in
/-- **Existence in Stacks 0GMG**, for a site given by a pretopology. -/
theorem nonempty_glueing_of_mem (hf : Presieve.ofArrows U f ∈ P X)
    (hρ : IsCocycle (X := pretopologyRingedSite P OC) f ρ)
    (hExt : ∀ (i : ι) {V : C} (a : V ⟶ U i) (n : ℤ), n < 0 →
      Subsingleton (DerivedCategory.Ext ((derivedOverMap.{0} (pretopologyRingedSite P OC) a).obj
        (E i)) ((derivedOverMap.{0} (pretopologyRingedSite P OC) a).obj (E i)) n))
    (hBound : ∃ t : ℤ, ∀ (i : ι) (n : ℤ), n < t →
      IsZero ((DerivedCategory.homologyFunctor _ n).obj (E i))) :
    Nonempty (Glueing (X := pretopologyRingedSite P OC) f E ρ) := by
  obtain ⟨M, ⟨σ⟩⟩ := exists_summandIdentification hf hρ hExt hBound
  exact ⟨⟨M, fun i => cechVertexIso (X := pretopologyRingedSite P OC) (E := E)
      (E' := fun i => (derivedOverMap.{0} (pretopologyRingedSite P OC) (f i)).obj M) f i
      (summandComparison hρ M σ ⦋0⦌ (cechVertex (X := pretopologyRingedSite P OC) f i)),
    cechVertexIso_compatible (X := pretopologyRingedSite P OC) (f := f) (E := E)
      (E' := fun i => (derivedOverMap.{0} (pretopologyRingedSite P OC) (f i)).obj M) (ρ := ρ)
      (ρ' := canonicalOverlap (X := pretopologyRingedSite P OC) f M) hρ
      (isCocycle_canonicalOverlap (X := pretopologyRingedSite P OC) f M)
      (fun i => summandComparison hρ M σ ⦋0⦌ (cechVertex (X := pretopologyRingedSite P OC) f i))
      (fun i j => summandComparison hρ M σ ⦋1⦌ (cechEdge (X := pretopologyRingedSite P OC) f i j))
      (fun i j => summandComparison_comm hρ M σ (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0)
        (cechEdge (X := pretopologyRingedSite P OC) f i j))
      (fun i j => summandComparison_comm hρ M σ (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)
        (cechEdge (X := pretopologyRingedSite P OC) f i j))⟩⟩

/-- The summandwise identification of the restriction of the global object of a glued pair
with the locally given objects of the covering: the canonical one, followed by the
identifications `ρ_i`. -/
def Glueing.summandIdentification (hρ : IsCocycle (X := pretopologyRingedSite P OC) f ρ)
    (A : Glueing (X := pretopologyRingedSite P OC) f E ρ) :
    (coveringLocallyGiven P OC f E ρ hρ).SummandIdentification
      (cechLift (X := pretopologyRingedSite P OC) f)
      ((cechTotalRestriction P OC f).mapDerivedCategory.obj A.obj) :=
  LocallyGiven.SummandIdentification.ofObjIso (G := globalLocallyGiven P OC f A.obj)
    (L := cechLift (X := pretopologyRingedSite P OC) f)
    (obj' := fun b => indexObj (X := pretopologyRingedSite P OC) f E
      (b : IndexCategory (X := pretopologyRingedSite P OC) f))
    (rho' := fun {b' b} g => indexRho (X := pretopologyRingedSite P OC) f E ρ
      (b := (b : IndexCategory (X := pretopologyRingedSite P OC) f))
      (b' := (b' : IndexCategory (X := pretopologyRingedSite P OC) f)) g)
    (cocycle' := (locallyGiven (X := pretopologyRingedSite P OC) f E ρ hρ).cocycle)
    (canonicalSummandIdentification P OC f A.obj)
    (fun b => ((pretopologyRingedSite P OC).derivedIteratedSliceTransport X
      (b : IndexCategory (X := pretopologyRingedSite P OC) f).V).mapIso
        ((derivedOverMap.{0} (pretopologyRingedSite P OC)
          (b : IndexCategory (X := pretopologyRingedSite P OC) f).a).mapIso
            (A.iso (b : IndexCategory (X := pretopologyRingedSite P OC) f).i)))
    (fun _ _ => indexRho_naturality (X := pretopologyRingedSite P OC) (E := E)
      (E' := fun i => (derivedOverMap.{0} (pretopologyRingedSite P OC) (f i)).obj A.obj) f ρ
      (canonicalOverlap (X := pretopologyRingedSite P OC) f A.obj) (fun i => (A.iso i).hom)
      A.compatibility _)

/-- **An isomorphism of glued pairs, read on the summands of the Čech object.** The restriction
to the total site of a morphism `e` of the global objects of two glued pairs is compatible with
their summandwise identifications on the summand `t` exactly when the restriction of `e` to
`U_{t_0}` is compatible with the identifications `ρ_{t_0}`, after restriction to the summand. -/
theorem Glueing.summandIdentification_iff (hρ : IsCocycle (X := pretopologyRingedSite P OC) f ρ)
    (A B : Glueing (X := pretopologyRingedSite P OC) f E ρ) (e : A.obj ⟶ B.obj)
    {ε : (cechTotalRestriction P OC f).mapDerivedCategory.obj A.obj ⟶
      (cechTotalRestriction P OC f).mapDerivedCategory.obj B.obj}
    (he : (cechTotalRestriction P OC f).mapDerivedCategory.map e = ε)
    (n : SimplexCategory) (t : ((cechLift (X := pretopologyRingedSite P OC) f).obj (op n)).I) :
    ((coveringLocallyGiven P OC f E ρ hρ).summandDerivedRestriction
        (cechLift (X := pretopologyRingedSite P OC) f) n t).map
        (((situation (overRingedSite P OC (X := X)).J ((coveringLocallyGiven P OC f E ρ hρ).image
          (cechLift (X := pretopologyRingedSite P OC) f))).derivedComponentModuleRestriction
          (structureSheaf (overRingedSite P OC (X := X)) ((coveringLocallyGiven P OC f E ρ hρ).image
            (cechLift (X := pretopologyRingedSite P OC) f))) n).map ε) ≫
        ((B.summandIdentification hρ).iso n t).hom = ((A.summandIdentification hρ).iso n t).hom ↔
      ((pretopologyRingedSite P OC).derivedIteratedSliceTransport X
          (((cechLift (X := pretopologyRingedSite P OC) f).obj (op n)).obj t).V).map
          ((derivedOverMap.{0} (pretopologyRingedSite P OC)
            (((cechLift (X := pretopologyRingedSite P OC) f).obj (op n)).obj t).a).map
              ((derivedOverMap.{0} (pretopologyRingedSite P OC) (f (t 0))).map e)) ≫
        ((pretopologyRingedSite P OC).derivedIteratedSliceTransport X
          (((cechLift (X := pretopologyRingedSite P OC) f).obj (op n)).obj t).V).map
          ((derivedOverMap.{0} (pretopologyRingedSite P OC)
            (((cechLift (X := pretopologyRingedSite P OC) f).obj (op n)).obj t).a).map
              (B.iso (t 0)).hom) =
      ((pretopologyRingedSite P OC).derivedIteratedSliceTransport X
          (((cechLift (X := pretopologyRingedSite P OC) f).obj (op n)).obj t).V).map
          ((derivedOverMap.{0} (pretopologyRingedSite P OC)
            (((cechLift (X := pretopologyRingedSite P OC) f).obj (op n)).obj t).a).map
              (A.iso (t 0)).hom) := by
  subst he
  exact comp_iff_of_naturality _ ((cechSummandIso P OC f n t).app A.obj) _ _ _ _
    ((cechSummandIso P OC f n t).hom.naturality e)

variable (P OC f E ρ) in
/-- **Uniqueness in Stacks 0GMG**, for a site given by a pretopology: two glued pairs are
isomorphic by exactly one isomorphism compatible with the identifications `ρ_i`. -/
theorem existsUnique_glueing_iso_of_mem (hf : Presieve.ofArrows U f ∈ P X)
    (hρ : IsCocycle (X := pretopologyRingedSite P OC) f ρ)
    (hExt : ∀ (i : ι) {V : C} (a : V ⟶ U i) (n : ℤ), n < 0 →
      Subsingleton (DerivedCategory.Ext ((derivedOverMap.{0} (pretopologyRingedSite P OC) a).obj
        (E i)) ((derivedOverMap.{0} (pretopologyRingedSite P OC) a).obj (E i)) n))
    (A B : Glueing (X := pretopologyRingedSite P OC) f E ρ) :
    ∃! e : A.obj ≅ B.obj, ∀ i : ι,
      (derivedOverMap.{0} (pretopologyRingedSite P OC) (f i)).map e.hom ≫ (B.iso i).hom =
        (A.iso i).hom := by
  obtain ⟨-, huniq⟩ :=
    (coveringLocallyGiven P OC f E ρ hρ).exists_unique_cartesian_summandIdentification
      (cechLift (X := pretopologyRingedSite P OC) f)
      (fun b t' ht' g => indexObj_shift_hom_eq_zero hExt b t' ht' g)
  obtain ⟨ε, hε, hεu⟩ := huniq _ _ (A.summandIdentification hρ).isCartesian
    (B.summandIdentification hρ).isCartesian (A.summandIdentification hρ)
    (B.summandIdentification hρ)
  let FF := cechTotalRestrictionFullyFaithful (OC := OC) hf
  refine ⟨FF.preimageIso ε, fun i => ?_, fun e he => ?_⟩
  · have := RingedSite.derivedIteratedSliceTransport_isEquivalence (pretopologyRingedSite P OC) X
      (((cechLift (X := pretopologyRingedSite P OC) f).obj (op ⦋0⦌)).obj
        (cechVertex (X := pretopologyRingedSite P OC) f i)).V
    exact comp_eq_of_map_comp_eq _ _
      (fun _ _ h => derivedOverMap_cechVertex_map_injective (X := pretopologyRingedSite P OC) f h)
      _ _ _ ((Glueing.summandIdentification_iff hρ A B (FF.preimage ε.hom) (FF.map_preimage _)
        ⦋0⦌ (cechVertex (X := pretopologyRingedSite P OC) f i)).1
          (hε ⦋0⦌ (cechVertex (X := pretopologyRingedSite P OC) f i)))
  · have h : (cechTotalRestriction P OC f).mapDerivedCategory.mapIso e = ε :=
      hεu _ fun n t => (Glueing.summandIdentification_iff hρ A B e.hom rfl n t).2
        (map_comp_eq_of_comp_eq _ _ _ _ _ (he _))
    ext
    exact FF.map_injective ((congrArg Iso.hom h).trans (FF.map_preimage ε.hom).symm)

/-- Let `(C, O_C)` be a ringed site with fibre products and `{U_i ⟶ X}_{i ∈ I}` a covering in
`C`. For `i ∈ I` let `E_i` be an object of `D(O_{U_i})` and for `i, j ∈ I` let
`ρ_{ij} : E_i|_{C/U_{ij}} ⟶ E_j|_{C/U_{ij}}` be an isomorphism in `D(O_{U_{ij}})`, where
`U_{ij} = U_i ×_X U_j`. Assume

1. the `ρ_{ij}` satisfy the cocycle condition on `U_i ×_X U_j ×_X U_k` for all `i, j, k ∈ I`,
2. `SheafExt^p_{O_{U_i}}(E_i, E_i) = 0` for all `p < 0` and `i ∈ I` (stated as the vanishing of
   the negative self-exts of `E_i|_{C/V}` for every object `V` over `U_i`), and
3. there exists a `t ∈ ℤ` such that `H^p(E_i) = 0` for `p < t` and all `i ∈ I`.

Then there exists a pair `(E, ρ_i)`, with `E` an object of `D(O_X)` and `ρ_i : E|_{U_i} ⟶ E_i`
isomorphisms in `D(O_{U_i})` compatible with the `ρ_{ij}`, and it is unique: two such pairs are
isomorphic by exactly one isomorphism compatible with the `ρ_i`. -/
@[stacks 0GMG]
theorem existsUnique_glueing {X : RingedSite.{u, u, u}} [hX : HasPullbacks X.C] {X₀ : X.C}
    {ι : Type u} {U : ι → X.C} (f : ∀ i, U i ⟶ X₀) (E : ∀ i, LocalDerivedCategory.{0} X (U i))
    (ρ : ∀ i j, (derivedOverMap.{0} X (pullback.fst (f i) (f j))).obj (E i) ≅
      (derivedOverMap.{0} X (pullback.snd (f i) (f j))).obj (E j))
    (hf : Sieve.generate (Presieve.ofArrows U f) ∈ X.J X₀)
    (hρ : IsCocycle f ρ)
    (hExt : ∀ (i : ι) {V : X.C} (a : V ⟶ U i) (n : ℤ), n < 0 →
      Subsingleton (DerivedCategory.Ext ((derivedOverMap.{0} X a).obj (E i))
        ((derivedOverMap.{0} X a).obj (E i)) n))
    (hBound : ∃ t : ℤ, ∀ (i : ι) (n : ℤ), n < t →
      IsZero ((DerivedCategory.homologyFunctor _ n).obj (E i))) :
    Nonempty (Glueing f E ρ) ∧
      ∀ A B : Glueing f E ρ, ∃! e : A.obj ≅ B.obj, ∀ i : ι,
        (derivedOverMap.{0} X (f i)).map e.hom ≫ (B.iso i).hom = (A.iso i).hom := by
  obtain ⟨C, J, O⟩ := X
  have hpb : HasPullbacks C := hX
  have hcov : Presieve.ofArrows U f ∈ J.toPretopology X₀ := hf
  clear hf
  have hP : J.toPretopology.toGrothendieck = J := (Pretopology.gi C).l_u_eq J
  revert O
  generalize J.toPretopology = P at hP ⊢
  subst hP
  intro O hX X₀ U f E ρ hρ hExt hBound hcov
  exact ⟨nonempty_glueing_of_mem P O f E ρ hcov hρ hExt hBound,
    existsUnique_glueing_iso_of_mem P O f E ρ hcov hρ hExt⟩

end AlgebraicGeometry.RingedSite.CoveringGlueing

end
