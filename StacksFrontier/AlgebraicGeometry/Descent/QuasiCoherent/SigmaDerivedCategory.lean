module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.SigmaComplexes
public import StacksFrontier.AlgebraicGeometry.Modules.SpecFieldDerivedPullback

/-!
# The derived category of a coproduct of schemes, read on the summands

Let `Z : I → Scheme` be a family of schemes. Restriction to the summands is an equivalence on
sheaves of modules (`AlgebraicGeometry.sigmaModulesEquivalence`) and on complexes of them
(`AlgebraicGeometry.sigmaComplexEquivalence`), for an arbitrary index type. It is *not* an
equivalence on derived categories: `D(𝒪_{∐ Z})` is not the product of the `D(𝒪_{Z i})`, and
Mathlib's `CategoryTheory.Functor.IsLocalization.pi` carries a finiteness hypothesis on the index
that an infinite family does not satisfy.

What does survive for an arbitrary family is **faithfulness**: the derived pullbacks along the
summand charts

  `D(𝒪_{∐ Z}) ⟶ ∏ᵢ D(𝒪_{Z i})`,  `F ↦ (L(ιᵢ)^* F)ᵢ`,

jointly distinguish morphisms. So an *equation* between two morphisms of `D(𝒪_{∐ Z})` may be
checked summand by summand, which is what an application that builds a commuting square over a
coproduct needs. Together with
`AlgebraicGeometry.nonempty_iso_Q_of_forall_iso_Q_sigmaι`, which glues a family of
isomorphisms of classes of complexes on the summands into one isomorphism over `∐ Z`, this is the
replacement for the product decomposition that does not exist.

## Main definitions

* `AlgebraicGeometry.derivedPullbackSigmaιFactors`: **the derived pullback along a summand chart
  is degreewise restriction**, as an isomorphism of functors
  `Q ⋙ L(ιᵢ)^* ≅ (ιᵢ^* on complexes) ⋙ Q`. No hypothesis on the complex: the chart is an open
  immersion, hence flat, so degreewise restriction along it is already exact.

## Main results

* `AlgebraicGeometry.nonempty_iso_Q_of_forall_iso_Q_sigmaι`: a family of isomorphisms
  `Q(K|ᵢ) ≅ Q(P|ᵢ)` between the classes of the summandwise restrictions of two complexes on
  `∐ Z` produces an isomorphism `Q(K) ≅ Q(P)`.
* `AlgebraicGeometry.eq_of_forall_map_eq_of_factors`: **faithfulness**, for any family of
  functors factoring degreewise restriction through `Q`.
* `AlgebraicGeometry.eq_of_forall_derivedPullback_sigmaι_map_eq`: **faithfulness for the derived
  pullbacks along the summand charts** — two morphisms of `D(𝒪_{∐ Z})` with the same derived
  pullback to every summand are equal.
* `AlgebraicGeometry.Q_map_eq_comp_of_forall_sigmaι`: faithfulness in the shape an application
  uses it — a map of complexes on `∐ Z` whose class is, summand by summand, the class of another
  one followed by the restriction of a given morphism of `D(𝒪_{∐ Z})`, has that factorization
  over `∐ Z`. The restriction itself is `AlgebraicGeometry.exists_restrict_sigmaι`.

## Implementation notes

The faithfulness argument is the calculus of fractions over the equivalence on complexes. Let
`f, g : Q(A) ⟶ Q(B)` agree on every summand. Two applications of `DerivedCategory.right_fac`
produce one complex `Y'`, a quasi-isomorphism `t : Y' ⟶ A` and two maps `u', v : Y' ⟶ B` with
`Q(t) ≫ f = Q(u')` and `Q(t) ≫ g = Q(v)`, so `f = g` reduces to `Q(u') = Q(v)`. Restricting to
the summand `i` and using the factorization gives `Q(u'|ᵢ) = Q(v|ᵢ)`, and the left calculus of
fractions for `HomotopyCategory.quasiIso` turns that into a quasi-isomorphism of complexes
`τᵢ : B|ᵢ ⟶ Yᵢ` with `u'|ᵢ ≫ τᵢ` and `v|ᵢ ≫ τᵢ` homotopic. The `Yᵢ` and the `τᵢ` glue to one
quasi-isomorphism `T : B ⟶ Y` over `∐ Z`, restriction to the summands being an equivalence on
complexes and quasi-isomorphy being detected summandwise
(`AlgebraicGeometry.quasiIso_of_quasiIso_pullback_sigmaι`); the homotopies glue by
`AlgebraicGeometry.sigmaHomotopy`. So `u' ≫ T` and `v ≫ T` are homotopic, hence have the same
class, and `Q(T)` is invertible.

The factorization of the derived pullback is uniqueness of left derived functors: degreewise
restriction along the chart is exact, so the functor it induces on derived categories is itself
a left derived functor of it, which is
`AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso`, and Mathlib's
`CategoryTheory.Functor.mapDerivedCategoryFactors` is the factorization of that induced functor.
Left exactness of degreewise restriction along the chart is flatness of the chart
(Stacks 02N4, `AlgebraicGeometry.preservesFiniteLimits_pullback_of_flat`); right exactness is
the pullback–pushforward adjunction.

## References

* [Stacks Project, Tag 02N4](https://stacks.math.columbia.edu/tag/02N4)
* [Stacks Project, Tag 06YF](https://stacks.math.columbia.edu/tag/06YF)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable {I : Type u} (Z : I → Scheme.{u})

/-- **The derived pullback along a summand chart of a coproduct of schemes is degreewise
restriction.** As an isomorphism of functors `CochainComplex (∐ Z).Modules ℤ ⥤ D(𝒪_{Z i})`,

  `Q ⋙ L(ιᵢ)^* ≅ (degreewise restriction to the summand `i`) ⋙ Q`,

with no hypothesis on the complex.

The chart `ιᵢ` is an open immersion, hence flat, so degreewise restriction along it is left
exact by [Stacks, Tag 02N4] and right exact as a left adjoint. An exact functor induces a
functor on derived categories which is a left derived functor of it, so uniqueness of left
derived functors identifies it with `L(ιᵢ)^*`
(`AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso`), and the induced functor factors
through `Q` by `CategoryTheory.Functor.mapDerivedCategoryFactors`. -/
def derivedPullbackSigmaιFactors (i : I) :
    DerivedCategory.Q ⋙ Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (Sigma.ι Z i).toLRSHom.toShHom ≅
      (Scheme.Modules.pullback (Sigma.ι Z i)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  letI : PreservesFiniteLimits (modulePullback (Sigma.ι Z i).toLRSHom.toShHom) :=
    preservesFiniteLimits_pullback_of_flat (Sigma.ι Z i)
  letI : (modulePullback (Sigma.ι Z i).toLRSHom.toShHom).IsLeftAdjoint :=
    ⟨_, ⟨modulePullbackPushforwardAdjunction _⟩⟩
  letI : PreservesFiniteColimits (modulePullback (Sigma.ι Z i).toLRSHom.toShHom) := inferInstance
  Functor.isoWhiskerLeft DerivedCategory.Q
      (SpecField.derivedPullbackMapDerivedIso (Sigma.ι Z i).toLRSHom.toShHom) ≪≫
    (modulePullback (Sigma.ι Z i).toLRSHom.toShHom).mapDerivedCategoryFactors

/-- A family of quasi-isomorphisms between the restrictions to the summands of two complexes on
`∐ Z` is the restriction of a quasi-isomorphism of complexes on `∐ Z`. -/
private theorem exists_quasiIso_of_forall_quasiIso
    {K L : CochainComplex (∐ Z : Scheme.{u}).Modules ℤ}
    (f : ∀ i, (sigmaComplexFunctor Z).obj K i ⟶ (sigmaComplexFunctor Z).obj L i)
    (hf : ∀ i, QuasiIso (f i)) : ∃ g : K ⟶ L, (∀ i, (sigmaComplexFunctor Z).map g i = f i) ∧
      QuasiIso g :=
  ⟨(sigmaComplexFunctor Z).preimage f, fun i => congrFun ((sigmaComplexFunctor Z).map_preimage _) i,
    quasiIso_of_quasiIso_pullback_sigmaι Z _ fun i => by
      rw [← sigmaComplexFunctor_map, (sigmaComplexFunctor Z).map_preimage]
      exact hf i⟩

/-- **Gluing a family of isomorphisms of classes of complexes on the summands.** Let `K` and `P`
be complexes on `∐ Z` whose degreewise restrictions to each summand have isomorphic classes in
the derived category of that summand. Then the classes of `K` and `P` are isomorphic in
`D(𝒪_{∐ Z})`.

Each isomorphism is a roof `K|ᵢ ⟵ Yᵢ ⟶ P|ᵢ` of actual complexes by
`DerivedCategory.right_fac`, with the left leg a quasi-isomorphism by construction and the right
leg one because its class is invertible. Degreewise restriction to the summands is an
equivalence, so the `Yᵢ` assemble into a complex on `∐ Z` and the two legs into maps of
complexes there; those are quasi-isomorphisms because they are so summand by summand
(`AlgebraicGeometry.quasiIso_of_quasiIso_pullback_sigmaι`). -/
theorem nonempty_iso_Q_of_forall_iso_Q_sigmaι
    (K P : CochainComplex (∐ Z : Scheme.{u}).Modules ℤ)
    (h : ∀ i, DerivedCategory.Q.obj ((sigmaComplexFunctor Z).obj K i) ≅
      DerivedCategory.Q.obj ((sigmaComplexFunctor Z).obj P i)) :
    Nonempty (DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj P) := by
  classical
  choose Y s hs t hroof using fun i => DerivedCategory.right_fac (h i).hom
  have htIso : ∀ i, IsIso (DerivedCategory.Q.map (t i)) := by
    intro i
    have ht : DerivedCategory.Q.map (t i) = DerivedCategory.Q.map (s i) ≫ (h i).hom := by
      rw [hroof i, IsIso.hom_inv_id_assoc]
    rw [ht]
    infer_instance
  have hsq : ∀ i, QuasiIso (s i) := fun i =>
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ (s i)).1 (hs i)
  have htq : ∀ i, QuasiIso (t i) := fun i =>
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ (t i)).1 (htIso i)
  set u := (sigmaComplexFunctor Z).objObjPreimageIso Y with hu
  obtain ⟨sg, -, hsgq⟩ := exists_quasiIso_of_forall_quasiIso Z
    (K := (sigmaComplexFunctor Z).objPreimage Y) (L := K)
    (fun i => (CategoryTheory.Pi.isoApp u i).hom ≫ s i) fun i => by
      have := hsq i
      infer_instance
  obtain ⟨tg, -, htgq⟩ := exists_quasiIso_of_forall_quasiIso Z
    (K := (sigmaComplexFunctor Z).objPreimage Y) (L := P)
    (fun i => (CategoryTheory.Pi.isoApp u i).hom ≫ t i) fun i => by
      have := htq i
      infer_instance
  have : IsIso (DerivedCategory.Q.map sg) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ sg).2 hsgq
  have : IsIso (DerivedCategory.Q.map tg) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ tg).2 htgq
  exact ⟨(asIso (DerivedCategory.Q.map sg)).symm ≪≫ asIso (DerivedCategory.Q.map tg)⟩

/-- **Faithfulness of restriction to the summands on the derived category, at classes of
complexes.** Let `G i` be functors `D(𝒪_{∐ Z}) ⥤ D(𝒪_{Z i})` each factoring degreewise
restriction to the summand `i` through `Q`. Two morphisms between classes of complexes on
`∐ Z` with the same image under every `G i` are equal.

See the implementation notes of this file for the argument. -/
theorem eq_of_forall_map_eq_of_factors_Q
    (G : ∀ i, DerivedCategory (∐ Z : Scheme.{u}).Modules ⥤ DerivedCategory (Z i).Modules)
    (κ : ∀ i, DerivedCategory.Q ⋙ G i ≅
      (Scheme.Modules.pullback (Sigma.ι Z i)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    {A B : CochainComplex (∐ Z : Scheme.{u}).Modules ℤ}
    (f g : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj B)
    (h : ∀ i, (G i).map f = (G i).map g) : f = g := by
  classical
  obtain ⟨Y, s, hs, u, hf⟩ := DerivedCategory.right_fac f
  obtain ⟨Y', s', hs', v, hg⟩ := DerivedCategory.right_fac (DerivedCategory.Q.map s ≫ g)
  have htIso : IsIso (DerivedCategory.Q.map (s' ≫ s)) := by
    rw [Functor.map_comp]; infer_instance
  have hfac : DerivedCategory.Q.map (s' ≫ s) ≫ f = DerivedCategory.Q.map (s' ≫ u) := by
    rw [hf, Functor.map_comp, Functor.map_comp, Category.assoc, IsIso.hom_inv_id_assoc]
  have hgac : DerivedCategory.Q.map (s' ≫ s) ≫ g = DerivedCategory.Q.map v := by
    rw [Functor.map_comp, Category.assoc, hg, IsIso.hom_inv_id_assoc]
  suffices hkey : DerivedCategory.Q.map (s' ≫ u) = DerivedCategory.Q.map v by
    rw [← cancel_epi (DerivedCategory.Q.map (s' ≫ s)), hfac, hgac, hkey]
  have hG : ∀ i, (G i).map (DerivedCategory.Q.map (s' ≫ u)) =
      (G i).map (DerivedCategory.Q.map v) := by
    intro i
    rw [← hfac, ← hgac, (G i).map_comp, (G i).map_comp, h i]
  have hQ : ∀ i, DerivedCategory.Q.map
        (((Scheme.Modules.pullback (Sigma.ι Z i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (s' ≫ u)) =
      DerivedCategory.Q.map
        (((Scheme.Modules.pullback (Sigma.ι Z i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map v) := by
    intro i
    have n1 := (κ i).hom.naturality (s' ≫ u)
    have n2 := (κ i).hom.naturality v
    simp only [Functor.comp_map] at n1 n2
    rw [← cancel_epi ((κ i).hom.app Y'), ← n1, ← n2, hG i]
  have hQh : ∀ i, DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (((Scheme.Modules.pullback (Sigma.ι Z i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (s' ≫ u))) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        (((Scheme.Modules.pullback (Sigma.ι Z i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map v)) := by
    intro i
    rw [← cancel_mono ((DerivedCategory.quotientCompQhIso (Z i).Modules).hom.app _),
      DerivedCategory.quotientCompQhIso_hom_naturality,
      DerivedCategory.quotientCompQhIso_hom_naturality, hQ i]
  have key : ∀ i, ∃ (Yc : CochainComplex (Z i).Modules ℤ)
      (τ : ((Scheme.Modules.pullback (Sigma.ι Z i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj B ⟶ Yc), QuasiIso τ ∧
      Nonempty (Homotopy ((((Scheme.Modules.pullback (Sigma.ι Z i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (s' ≫ u)) ≫ τ)
        ((((Scheme.Modules.pullback (Sigma.ι Z i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map v) ≫ τ)) := by
    intro i
    obtain ⟨Yh, σ, hσ, hcomm⟩ := (MorphismProperty.map_eq_iff_postcomp DerivedCategory.Qh
      (HomotopyCategory.quasiIso (Z i).Modules (ComplexShape.up ℤ)) _ _).1 (hQh i)
    obtain ⟨Yc, rfl⟩ := HomotopyCategory.quotient_obj_surjective Yh
    obtain ⟨τ, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective σ
    refine ⟨Yc, τ, ?_, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
    · rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff,
        HomologicalComplex.mem_quasiIso_iff] at hσ
    · simpa only [Functor.map_comp] using hcomm
  choose Yc τ hτ Hτ using key
  set wi := (sigmaComplexFunctor Z).objObjPreimageIso Yc with hwi
  obtain ⟨T, hT, hTq⟩ := exists_quasiIso_of_forall_quasiIso Z
    (K := B) (L := (sigmaComplexFunctor Z).objPreimage Yc)
    (fun i => τ i ≫ (CategoryTheory.Pi.isoApp wi i).inv) fun i => by
      have := hτ i
      exact inferInstanceAs (QuasiIso (τ i ≫ (CategoryTheory.Pi.isoApp wi i).inv))
  have Hfin : ∀ i, Homotopy ((sigmaComplexFunctor Z).map ((s' ≫ u) ≫ T) i)
      ((sigmaComplexFunctor Z).map (v ≫ T) i) := by
    intro i
    refine (Homotopy.ofEq ?_).trans
      (((Hτ i).some.compRight ((CategoryTheory.Pi.isoApp wi i).inv)).trans (Homotopy.ofEq ?_))
    · rw [sigmaComplexFunctor_map, Functor.map_comp]
      exact (congrArg _ (hT i)).trans (Category.assoc _ _ _).symm
    · rw [sigmaComplexFunctor_map, Functor.map_comp]
      exact (Category.assoc _ _ _).trans (congrArg _ (hT i).symm)
  have hfinal := DerivedCategory.Q_map_eq_of_homotopy _ (sigmaHomotopy Z Hfin)
  rw [DerivedCategory.Q.map_comp (s' ≫ u) T, DerivedCategory.Q.map_comp v T] at hfinal
  have : IsIso (DerivedCategory.Q.map T) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ T).2 hTq
  exact (cancel_mono (DerivedCategory.Q.map T)).1 hfinal

/-- **Faithfulness of restriction to the summands on the derived category.** Let `G i` be
functors `D(𝒪_{∐ Z}) ⥤ D(𝒪_{Z i})` each factoring degreewise restriction to the summand `i`
through `Q`. Two morphisms of `D(𝒪_{∐ Z})` with the same image under every `G i` are equal.

Every object of the derived category is isomorphic to the class of a complex, so this is
`AlgebraicGeometry.eq_of_forall_map_eq_of_factors_Q` conjugated by two such isomorphisms. -/
theorem eq_of_forall_map_eq_of_factors
    (G : ∀ i, DerivedCategory (∐ Z : Scheme.{u}).Modules ⥤ DerivedCategory (Z i).Modules)
    (κ : ∀ i, DerivedCategory.Q ⋙ G i ≅
      (Scheme.Modules.pullback (Sigma.ι Z i)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    {A B : DerivedCategory (∐ Z : Scheme.{u}).Modules} {f g : A ⟶ B}
    (h : ∀ i, (G i).map f = (G i).map g) : f = g := by
  obtain ⟨A', ⟨a⟩⟩ : ∃ A', Nonempty (DerivedCategory.Q.obj A' ≅ A) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso A⟩⟩
  obtain ⟨B', ⟨b⟩⟩ : ∃ B', Nonempty (DerivedCategory.Q.obj B' ≅ B) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso B⟩⟩
  have key : a.hom ≫ f ≫ b.inv = a.hom ≫ g ≫ b.inv := by
    refine eq_of_forall_map_eq_of_factors_Q Z G κ _ _ fun i => ?_
    rw [(G i).map_comp, (G i).map_comp, (G i).map_comp, (G i).map_comp, h i]
  exact (cancel_mono b.inv).1 ((cancel_epi a.hom).1 key)

/-- **The derived pullbacks along the summand charts of a coproduct of schemes are jointly
faithful.** Two morphisms of `D(𝒪_{∐ Z})` whose derived pullbacks to every summand agree are
equal. The index type is arbitrary, and there is no hypothesis on the family of schemes.

This is `AlgebraicGeometry.eq_of_forall_map_eq_of_factors` at the factorization
`AlgebraicGeometry.derivedPullbackSigmaιFactors`. -/
theorem eq_of_forall_derivedPullback_sigmaι_map_eq
    {A B : DerivedCategory (∐ Z : Scheme.{u}).Modules} {f g : A ⟶ B}
    (h : ∀ i, (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (Sigma.ι Z i).toLRSHom.toShHom).map f =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (Sigma.ι Z i).toLRSHom.toShHom).map g) : f = g :=
  eq_of_forall_map_eq_of_factors Z
    (fun i => Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (Sigma.ι Z i).toLRSHom.toShHom) (derivedPullbackSigmaιFactors Z) h

/-- A morphism `L(S(a))` is a composite `L(S(p) ≫ β)` as soon as the functor `T` through which
`S ⋙ L` factors says so: `bi` is the morphism `β` reads as through the factorization, and the
hypotheses are that it does so (`hbi`) and that it exhibits `T(a)` as `T(p) ≫ bi` (`h`). -/
private theorem map_eq_comp_of_natIso {C D E : Type*} [Category C] [Category D] [Category E]
    {S : C ⥤ D} {L : D ⥤ E} {T : C ⥤ E} (κ : S ⋙ L ≅ T)
    {A B F : C} (p : A ⟶ B) (a : A ⟶ F) (β : S.obj B ⟶ S.obj F) (bi : T.obj B ⟶ T.obj F)
    (hbi : κ.hom.app B ≫ bi = L.map β ≫ κ.hom.app F) (h : T.map a = T.map p ≫ bi) :
    L.map (S.map a) = L.map (S.map p ≫ β) := by
  rw [Functor.map_comp]
  refine (cancel_mono (κ.hom.app F)).1 ?_
  refine (κ.hom.naturality a).trans ?_
  rw [h, ← Category.assoc, ← κ.hom.naturality p, Category.assoc, hbi, ← Category.assoc]
  rfl

/-- **Recognizing a morphism of `D(𝒪_{∐ Z})` as `Q` of a map of complexes, summand by summand.**
Let `p : A ⟶ B` and `a : A ⟶ C` be maps of complexes on `∐ Z`, let `β : Q(B) ⟶ Q(C)` and let
`bi i : Q(B|ᵢ) ⟶ Q(C|ᵢ)` be what `β` reads as on the summand `i` through
`AlgebraicGeometry.derivedPullbackSigmaιFactors` (that is `hbi`). If the class of `a` on every
summand is the class of `p` there followed by `bi i`, then `Q(a) = Q(p) ≫ β`.

This is the shape in which an application builds a commuting square over a coproduct: the
hypothesis `h` is a statement about maps of complexes on the summands, and the conclusion an
equation in `D(𝒪_{∐ Z})`. It is
`AlgebraicGeometry.eq_of_forall_derivedPullback_sigmaι_map_eq` with the factorization applied at
each summand. -/
theorem Q_map_eq_comp_of_forall_sigmaι {A B C : CochainComplex (∐ Z : Scheme.{u}).Modules ℤ}
    (p : A ⟶ B) (a : A ⟶ C) (β : DerivedCategory.Q.obj B ⟶ DerivedCategory.Q.obj C)
    (bi : ∀ i, DerivedCategory.Q.obj ((sigmaComplexFunctor Z).obj B i) ⟶
      DerivedCategory.Q.obj ((sigmaComplexFunctor Z).obj C i))
    (hbi : ∀ i, (derivedPullbackSigmaιFactors Z i).hom.app B ≫ bi i =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (Sigma.ι Z i).toLRSHom.toShHom).map β ≫ (derivedPullbackSigmaιFactors Z i).hom.app C)
    (h : ∀ i, DerivedCategory.Q.map
        (((Scheme.Modules.pullback (Sigma.ι Z i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map a) =
      DerivedCategory.Q.map (((Scheme.Modules.pullback (Sigma.ι Z i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map p) ≫ bi i) :
    DerivedCategory.Q.map a = DerivedCategory.Q.map p ≫ β :=
  eq_of_forall_derivedPullback_sigmaι_map_eq Z fun i =>
    map_eq_comp_of_natIso (derivedPullbackSigmaιFactors Z i) p a β (bi i) (hbi i) (h i)

/-- **The morphism a morphism of `D(𝒪_{∐ Z})` reads as on a summand.** Conjugating by the
factorization `AlgebraicGeometry.derivedPullbackSigmaιFactors` turns the derived pullback of
`β` to the summand `i` into a morphism between the classes of the degreewise restrictions,
which is the datum `AlgebraicGeometry.Q_map_eq_comp_of_forall_sigmaι` asks for. -/
theorem exists_restrict_sigmaι {B C : CochainComplex (∐ Z : Scheme.{u}).Modules ℤ}
    (β : DerivedCategory.Q.obj B ⟶ DerivedCategory.Q.obj C) :
    ∃ bi : ∀ i, DerivedCategory.Q.obj ((sigmaComplexFunctor Z).obj B i) ⟶
      DerivedCategory.Q.obj ((sigmaComplexFunctor Z).obj C i),
      ∀ i, (derivedPullbackSigmaιFactors Z i).hom.app B ≫ bi i =
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (Sigma.ι Z i).toLRSHom.toShHom).map β ≫ (derivedPullbackSigmaιFactors Z i).hom.app C :=
  ⟨fun i => (derivedPullbackSigmaιFactors Z i).inv.app B ≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (Sigma.ι Z i).toLRSHom.toShHom).map β ≫ (derivedPullbackSigmaιFactors Z i).hom.app C,
    fun _ => Iso.hom_inv_id_app_assoc _ _ _⟩

end AlgebraicGeometry

end
