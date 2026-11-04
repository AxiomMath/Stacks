module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum

/-!
# Maps from an affine formal spectrum to an affine scheme (Stacks 0AQF)

Let `A` be a weakly admissible topological `S`-algebra and let `X` be an *affine* scheme over
`S`. **Stacks 0AQF** says that restriction along the quotient maps

`Mor_S(Spec A, X) ⟶ Mor_S(Spf A, X)`

is a bijection.

The Stacks proof goes through Stacks 0AN0: for `X = Spec Λ` affine, a morphism `Spf A ⟶ Spec Λ`
is a continuous `S`-algebra map `Λ → A` with `Λ` discrete, which is just an `S`-algebra map, and
those are the morphisms `Spec A ⟶ Spec Λ`. The proof folded here runs that argument directly in
terms of the quotients, which is why it needs no separate 0AN0: a morphism out of `Spf A` is, by
the colimit, a compatible family of morphisms `Spec (A ⧸ I) ⟶ X`, equivalently a compatible
family of ring maps `Λ → A ⧸ I`.

*Injectivity* is `hom_eq_of_weak_ideal_quotients`: two elements of `A` with the same class modulo
every weak ideal of definition are equal, because `A` is separated and the weak ideals of
definition form a basis of neighbourhoods of `0`.

*Surjectivity* is the lift: a compatible family `Λ → A ⧸ I` is a map into `lim A ⧸ I`, and that
limit is `A` by completeness and separatedness. The resulting map `Λ → A` lands where it should
because an element of a weak ideal of definition is topologically nilpotent, so it lies in the
Jacobson radical of each quotient — which is what makes the induced `Spec A ⟶ X` land in `X`
rather than merely in some open of it.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_formalSpectrumToSpec`: **Stacks 0AQF**, the canonical map
  `Spf A ⟶ Spec A`, characterised on every quotient stage.
* `AlgebraicGeometry.FormalSpace.bijective_map_into_affine`: **Stacks 0AQF**, the bijection.
* `AlgebraicGeometry.FormalSpace.eq_of_weak_ideal_submem'` and
  `AlgebraicGeometry.FormalSpace.exists_lift_compatible_weak_quotients'`: separatedness and
  completeness of a weakly admissible ring in the form used throughout — an element is
  determined by its classes modulo the weak ideals of definition, and every compatible family
  of such classes comes from an element.

## Implementation notes

The source of the morphism set is the category of *all* schemes over `S`: only `X` and the
quotient spectra are required to lie in the chosen big fppf site, and `Spec A` itself need not.
That is why restriction is given as
`AlgebraicGeometry.FormalSpace.restrictToFormalSpectrum`, defined directly by `colimit.desc` out
of the cocone of quotient-stage restrictions, rather than as composition with a
formal-to-ordinary-spectrum morphism. When `Spec A` *does* belong to the site the two agree, and
that is `AlgebraicGeometry.FormalSpace.restrictToFormalSpectrum_eq`.

The over-`S` structure on `Spec A` and its compatibility with the quotient maps (`fA`, `hcompat`)
are explicit hypotheses throughout, because `AlgebraicGeometry.FormalSpace.QuotientSystem`
records only the structure morphisms *of the quotients*; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum`.

## References

* [Stacks Project, Tag 0AQF](https://stacks.math.columbia.edu/tag/0AQF)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal Opposite
open Filter
open scoped Topology

namespace AlgebraicGeometry.FormalSpace

universe u


variable {B : BigFppfSite.{u}} {S : Scheme.{u}}
  {hS : B.Contains S} {A : Type u} [CommRing A] [TopologicalSpace A]

/-- Restrict a scheme map over `S` to a quotient stage, which is an object of
the site even when `Spec A` is not. -/
public def stageRestriction (D : QuotientSystem B S hS A)
    (fA : Spec (.of A) ⟶ S)
    (hcompat : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ fA = D.overS J)
    (X : BigFppfOver B S hS)
    (f : (Over.mk fA : Over S) ⟶ (Over.post B.inclusion).obj X)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    (BigAffineFppf.inclusion B S hS).obj (D.stage J) ⟶ X :=
  Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ f.left)) (by
      exact ObjectProperty.hom_ext _ <| (Category.assoc _ _ _).trans
        ((congrArg (fun t => Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ t)
          f.w).trans (hcompat J)))

/-- The cocone of restrictions of an ordinary scheme map to the quotient
spectra. -/
public def restrictionCocone (D : QuotientSystem B S hS A)
    (fA : Spec (.of A) ⟶ S)
    (hcompat : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ fA = D.overS J)
    (X : BigFppfOver B S hS)
    (f : (Over.mk fA : Over S) ⟶ (Over.post B.inclusion).obj X) :
    Cocone (formalSpectrumDiagram D) where
  pt := (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj X
  ι := {
    app := fun J ↦ (Sheaf.sheafifiedYoneda
      (BigFppfOver.topology B S hS)).map
        (stageRestriction D fA hcompat X f J)
    naturality := by
      intro J L g
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
        Functor.comp_map, ← Functor.map_comp]
      congr 1
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (leOfHom g))) ≫
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk L.1)) ≫ f.left) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ f.left
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        Ideal.Quotient.factor_comp_mk] }

/-- Restriction from the ordinary spectrum to the formal spectrum. The source
is an ordinary scheme over `S` and need not be an object of the chosen site. -/
public def restrictToFormalSpectrum (D : QuotientSystem B S hS A)
    (fA : Spec (.of A) ⟶ S)
    (hcompat : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ fA = D.overS J)
    (X : BigFppfOver B S hS)
    (f : (Over.mk fA : Over S) ⟶ (Over.post B.inclusion).obj X) :
    formalSpectrum D ⟶
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj X :=
  colimit.desc _ (restrictionCocone D fA hcompat X f)

/-- Restriction to the formal spectrum is characterized on each quotient
stage by the usual quotient-spectrum morphism. -/
public theorem restrictToFormalSpectrum_spec
    (D : QuotientSystem B S hS A) (fA : Spec (.of A) ⟶ S)
    (hcompat : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ fA = D.overS J)
    (X : BigFppfOver B S hS)
    (f : (Over.mk fA : Over S) ⟶ (Over.post B.inclusion).obj X)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    formalSpectrumInclusion D (OrderDual.toDual J) ≫
        restrictToFormalSpectrum D fA hcompat X f =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (stageRestriction D fA hcompat X f J) :=
  colimit.ι_desc (restrictionCocone D fA hcompat X f) (OrderDual.toDual J)

/-- The ordinary spectrum of a topological `S`-algebra, as an object of the
big affine fppf site over `S`. -/
public def specOver (hAS : B.Contains (Spec (.of A)))
    (fA : Spec (.of A) ⟶ S) : BigAffineFppf B S hS :=
  ⟨Over.mk (ObjectProperty.homMk fA : B.obj hAS ⟶ B.obj hS), by
    change IsAffine (Spec (.of A))
    infer_instance⟩

/-- The canonical quotient-spectrum map, compatible with the chosen
`S`-scheme structure on the ordinary spectrum. -/
public def stageToSpec (D : QuotientSystem B S hS A)
    (hAS : B.Contains (Spec (.of A))) (fA : Spec (.of A) ⟶ S)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
    (hJ : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ fA =
      D.overS J) : D.stage J ⟶ specOver hAS fA :=
  ObjectProperty.homMk <| Over.homMk
    (U := (D.stage J).1) (V := (specOver hAS fA).1)
    (ObjectProperty.homMk
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1))))
    (by apply ObjectProperty.hom_ext; exact hJ)

private abbrev affineTargetRing (X : BigAffineFppf B S hS) :=
  ↑(Scheme.Γ.obj (Opposite.op ((BigAffineFppf.toScheme B S hS).obj X)))

/-- The canonical formal-to-ordinary-spectrum map exists and restricts to the
quotient-spectrum map at every stage. -/
@[stacks 0AQF "canonical map"]
public theorem exists_formalSpectrumToSpec
    (D : QuotientSystem B S hS A)
    (hAS : B.Contains (Spec (.of A))) (fA : Spec (.of A) ⟶ S)
    (hcompat : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ fA = D.overS J) :
    ∃ q : formalSpectrum D ⟶
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (specOver hAS fA)),
      ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
        formalSpectrumInclusion D (OrderDual.toDual J) ≫ q =
          (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
            ((BigAffineFppf.inclusion B S hS).map
              (stageToSpec D hAS fA J (hcompat J))) := by
  refine ⟨restrictToFormalSpectrum D fA hcompat (specOver hAS fA).obj
    (𝟙 (Over.mk fA)), ?_⟩
  intro J
  refine (restrictToFormalSpectrum_spec D fA hcompat (specOver hAS fA).obj
    (𝟙 (Over.mk fA)) J).trans ?_
  congr 1

/-- The map from the formal spectrum to the ordinary spectrum induced by the
canonical quotient-spectrum maps. -/
public def formalSpectrumToSpec
    (D : QuotientSystem B S hS A)
    (hAS : B.Contains (Spec (.of A))) (fA : Spec (.of A) ⟶ S)
    (hcompat : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ fA = D.overS J) :
    formalSpectrum D ⟶
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (specOver hAS fA)) :=
  Classical.choose (exists_formalSpectrumToSpec D hAS fA hcompat)

/-- On every quotient stage, the formal-to-ordinary-spectrum map is the
usual quotient-spectrum morphism. -/
public theorem formalSpectrumToSpec_spec
    (D : QuotientSystem B S hS A)
    (hAS : B.Contains (Spec (.of A))) (fA : Spec (.of A) ⟶ S)
    (hcompat : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ fA = D.overS J)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    formalSpectrumInclusion D (OrderDual.toDual J) ≫
      formalSpectrumToSpec D hAS fA hcompat =
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map
            (stageToSpec D hAS fA J (hcompat J))) :=
  (Classical.choose_spec (exists_formalSpectrumToSpec D hAS fA hcompat)) J

/-- When the ordinary spectrum belongs to the site, quotient-stage
restriction agrees with composition with the canonical map from the formal
spectrum. -/
public theorem restrictToFormalSpectrum_eq
    (D : QuotientSystem B S hS A)
    (hAS : B.Contains (Spec (.of A))) (fA : Spec (.of A) ⟶ S)
    (hcompat : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ fA = D.overS J)
    (X : BigFppfOver B S hS)
    (f : (specOver hAS fA).obj ⟶ X) :
    restrictToFormalSpectrum D fA hcompat X ((Over.post B.inclusion).map f) =
      formalSpectrumToSpec D hAS fA hcompat ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map f := by
  apply colimit.hom_ext
  intro J
  change formalSpectrumInclusion D J ≫ _ =
    formalSpectrumInclusion D J ≫ _
  refine (restrictToFormalSpectrum_spec D fA hcompat X
    ((Over.post B.inclusion).map f) J).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg
    (fun t => t ≫ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map f)
    (formalSpectrumToSpec_spec D hAS fA hcompat J).symm)
  exact (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_comp
    ((BigAffineFppf.inclusion B S hS).map (stageToSpec D hAS fA J (hcompat J))) f

private theorem eq_of_weak_ideal_submem
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {x y : A}
    (h : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      x - y ∈ J.1) : x = y := by
  have hnbhd : ∀ V ∈ 𝓝 (0 : A), x - y ∈ V := by
    intro V hV
    obtain ⟨U, hU⟩ := (isLinearTopology_iff_hasBasis_open_ideal.mp inferInstance).mem_iff.mp hV
    obtain ⟨I, hI⟩ := hA.1
    exact hU.2 (h ⟨I ⊓ U, ⟨hI.1.inter hU.1, fun z hz => hI.2 z hz.1⟩⟩).2
  have : T2Space A := hA.2.2
  rw [← sub_eq_zero]
  by_contra hne
  obtain ⟨U, V, hU, hV, hUV⟩ :=
    t2_separation_nhds (x := 0) (y := x - y) (by simpa [eq_comm] using hne)
  exact Set.disjoint_left.mp hUV (hnbhd U hU) (mem_of_mem_nhds hV)

/-- In a weakly admissible ring, two elements whose difference lies in every weak ideal of
definition are equal. -/
public alias eq_of_weak_ideal_submem' := eq_of_weak_ideal_submem

/-- In a weakly admissible ring, elements with the same class modulo every weak ideal of
definition are equal. -/
private theorem eq_of_weak_quotient_mk_eq
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {x y : A}
    (h : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      Ideal.Quotient.mk J.1 x = Ideal.Quotient.mk J.1 y) : x = y :=
  eq_of_weak_ideal_submem hA fun J => Ideal.Quotient.eq.mp (h J)

-- The Cauchy-net argument elaborates both the order-dual index and its uniform structure.
private theorem exists_lift_compatible_weak_quotients
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (b : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }, A ⧸ J.1)
    (hb : ∀ (J L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
      (h : J.1 ≤ L.1), Ideal.Quotient.factor h (b J) = b L) :
    ∃ a : A, ∀ J, Ideal.Quotient.mk J.1 a = b J := by
  classical
  let W := { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }
  let : SemilatticeInf W := {
    inf := fun J L => ⟨J.1 ⊓ L.1, ⟨J.2.1.inter L.2.1, fun x hx => J.2.2 x hx.1⟩⟩
    inf_le_left := fun J K => show (J.1 ⊓ K.1) ≤ J.1 from inf_le_left
    inf_le_right := fun J K => show (J.1 ⊓ K.1) ≤ K.1 from inf_le_right
    le_inf := fun J K L hJ hL => show J.1 ≤ K.1 ⊓ L.1 from le_inf hJ hL
  }
  let β := OrderDual W
  obtain ⟨I₀, hI₀⟩ := hA.1
  have : Nonempty β := ⟨OrderDual.toDual ⟨I₀, hI₀⟩⟩
  let : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  let u : β → A := fun i => Classical.choose
    (Ideal.Quotient.mk_surjective (b (OrderDual.ofDual i)))
  have hu (i : β) : Ideal.Quotient.mk (OrderDual.ofDual i).1 (u i) =
      b (OrderDual.ofDual i) := Classical.choose_spec
        (Ideal.Quotient.mk_surjective (b (OrderDual.ofDual i)))
  have hmk (i : β) (J : W) (h : OrderDual.ofDual i ≤ J) :
      Ideal.Quotient.mk J.1 (u i) = b J := by
    rw [← Ideal.Quotient.factor_mk h, hu, hb _ _ h]
  have hcu : CauchySeq u := by
    rw [cauchySeq_iff_tendsto, uniformity_eq_comap_neg_add_nhds_zero, Filter.tendsto_comap_iff]
    change Tendsto (fun p : β × β => -u p.1 + u p.2) atTop (𝓝 0)
    apply (IsLinearTopology.hasBasis_open_ideal (R := A)).tendsto_right_iff.mpr
    intro L hL
    let JL : W := ⟨L ⊓ I₀,
      ⟨hL.inter hI₀.1, fun x hx => hI₀.2 x hx.2⟩⟩
    have hev : ∀ᶠ p : β × β in atTop,
        OrderDual.toDual JL ≤ p.1 ∧ OrderDual.toDual JL ≤ p.2 :=
      (atTop_basis (α := β × β)).mem_iff.mpr
        ⟨(OrderDual.toDual JL, OrderDual.toDual JL), trivial, fun p hp => ⟨hp.1, hp.2⟩⟩
    filter_upwards [hev] with p hp
    have hi : OrderDual.ofDual p.1 ≤ JL := OrderDual.ofDual_le_ofDual.mpr hp.1
    have hj : OrderDual.ofDual p.2 ≤ JL := OrderDual.ofDual_le_ofDual.mpr hp.2
    have hmem : u p.1 - u p.2 ∈ L ⊓ I₀ :=
      Ideal.Quotient.eq.mp ((hmk _ _ hi).trans (hmk _ _ hj).symm)
    change -u p.1 + u p.2 ∈ L
    convert L.neg_mem hmem.1 using 1
    ring
  have : CompleteSpace A := hA.2.1
  obtain ⟨a, ha⟩ := CompleteSpace.complete hcu
  have hlim : Tendsto u atTop (𝓝 a) := ha
  refine ⟨a, fun J => ?_⟩
  obtain ⟨aJ, haJ⟩ := Ideal.Quotient.mk_surjective (b J)
  have hev : ∀ᶠ i : β in atTop, OrderDual.toDual J ≤ i :=
    (atTop_basis (α := β)).mem_iff.mpr ⟨OrderDual.toDual J, trivial, subset_rfl⟩
  have hevent : ∀ᶠ i : β in atTop, u i - aJ ∈ J.1 := by
    filter_upwards [hev] with i hi
    have hKi : OrderDual.ofDual i ≤ J := OrderDual.ofDual_le_ofDual.mpr hi
    exact Ideal.Quotient.eq.mp ((hmk _ _ hKi).trans haJ.symm)
  have hclosed : IsClosed (J.1 : Set A) :=
    J.1.toAddSubgroup.isClosed_of_isOpen J.2.1
  have hsub : Tendsto (fun i : β => u i - aJ) atTop (𝓝 (a - aJ)) := by
    simpa using hlim.sub tendsto_const_nhds
  rw [← haJ, Ideal.Quotient.eq]
  exact hclosed.mem_of_tendsto hsub hevent

/-- In a weakly admissible ring `A`, a family of classes modulo the weak ideals of definition
that is compatible under the quotient maps comes from a single element of `A`. -/
public alias exists_lift_compatible_weak_quotients' := exists_lift_compatible_weak_quotients

private noncomputable def lift_compatible_weak_quotient_ring_homs
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    {C : Type u} [CommRing C]
    (f : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }, C →+* A ⧸ J.1)
    (hf : ∀ (J L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
      (h : J.1 ≤ L.1), (Ideal.Quotient.factor h).comp (f J) = f L) : C →+* A := by
  classical
  let a (c : C) : A := Classical.choose <| exists_lift_compatible_weak_quotients hA
    (fun J => f J c) (fun J L h => RingHom.congr_fun (hf J L h) c)
  have ha (c : C) (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
      Ideal.Quotient.mk J.1 (a c) = f J c :=
    Classical.choose_spec (exists_lift_compatible_weak_quotients hA
      (fun K => f K c) (fun K L h => RingHom.congr_fun (hf K L h) c)) J
  refine {
    toFun := a
    map_zero' := ?_
    map_one' := ?_
    map_add' := ?_
    map_mul' := ?_ }
  · exact eq_of_weak_quotient_mk_eq hA fun J => by simp [ha]
  · exact fun x y => eq_of_weak_quotient_mk_eq hA fun J => by simp [ha]
  · exact eq_of_weak_quotient_mk_eq hA fun J => by simp [ha]
  · exact fun x y => eq_of_weak_quotient_mk_eq hA fun J => by simp [ha]

private theorem lift_compatible_weak_quotient_ring_homs_spec
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    {C : Type u} [CommRing C]
    (f : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }, C →+* A ⧸ J.1)
    (hf : ∀ (J L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
      (h : J.1 ≤ L.1), (Ideal.Quotient.factor h).comp (f J) = f L)
    (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
    (Ideal.Quotient.mk J.1).comp
      (lift_compatible_weak_quotient_ring_homs hA f hf) = f J := by
  classical
  ext c
  exact Classical.choose_spec (exists_lift_compatible_weak_quotients hA
    (fun K => f K c) (fun K L h => RingHom.congr_fun (hf K L h) c)) J

private theorem isUnit_of_weak_quotients
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (a : A)
    (ha : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      IsUnit (Ideal.Quotient.mk J.1 a)) : IsUnit a := by
  classical
  obtain ⟨b, hb⟩ := exists_lift_compatible_weak_quotients hA
    (fun J => Ring.inverse (Ideal.Quotient.mk J.1 a)) (by
      intro J L h
      apply (ha L).mul_left_cancel
      rw [Ring.mul_inverse_cancel _ (ha L), ← Ideal.Quotient.factor_mk h,
        ← map_mul, Ring.mul_inverse_cancel _ (ha J), map_one])
  apply isUnit_iff_exists_inv.mpr
  refine ⟨b, eq_of_weak_quotient_mk_eq hA (fun J => ?_)⟩
  rw [map_mul, hb, Ring.mul_inverse_cancel _ (ha J), map_one]

private theorem topologicallyNilpotent_mem_jacobson
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) {a : A}
    (ha : IsTopologicallyNilpotent a) : a ∈ Ideal.jacobson (⊥ : Ideal A) := by
  rw [Ideal.mem_jacobson_bot]
  intro b
  apply isUnit_of_weak_quotients hA
  intro J
  obtain ⟨n, hn⟩ := (ha.mul_right b).exists_pow_mem_of_mem_nhds
    (J.2.1.mem_nhds (J.1.zero_mem))
  have hn' : IsNilpotent (Ideal.Quotient.mk J.1 (a * b)) :=
    ⟨n, by rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]; exact hn⟩
  simpa only [map_add, map_one] using hn'.isUnit_add_one

private theorem open_eq_top_of_weak_quotients
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (U : (Spec (.of A)).Opens)
    (hU : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1))) ⊆ U) :
    U = ⊤ := by
  apply top_le_iff.mp
  intro p _
  obtain ⟨M, hM, hpM⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
  let m : PrimeSpectrum A := ⟨M, hM.isPrime⟩
  have hpm : p ⤳ m := (PrimeSpectrum.le_iff_specializes p m).mp hpM
  obtain ⟨I, hI⟩ := hA.1
  refine hpm.mem_open U.isOpen (hU ⟨I, hI⟩ ?_)
  change m ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I))
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  exact fun a ha => (show Ideal.jacobson (⊥ : Ideal A) ≤ M from
    sInf_le ⟨bot_le, hM⟩) (topologicallyNilpotent_mem_jacobson hA (hI.2 a ha))

private theorem hom_eq_of_weak_ideal_quotients
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    {Y : Scheme.{u}} (f g : Spec (.of A) ⟶ Y)
    (h : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ f =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ g) :
    f = g := by
  let i := equalizer.ι f g
  let l (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :=
    equalizer.lift (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1))) (h J)
  have hl (J) : l J ≫ i = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) :=
    equalizer.lift_ι _ _
  have hU : i.coborderRange = ⊤ := by
    refine open_eq_top_of_weak_quotients hA _ fun J => ?_
    rintro _ ⟨x, rfl⟩
    exact subset_coborder ⟨l J x, by rw [← Scheme.Hom.comp_apply, hl]⟩
  have : IsClosedImmersion i := by
    have : IsIso i.coborderRange.ι := by
      rw [hU, ← Scheme.topIso_hom]
      infer_instance
    rw [← i.liftCoborder_ι]
    infer_instance
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.mp (inferInstance : IsClosedImmersion i)
  have hI : I = ⊥ := by
    apply le_bot_iff.mp
    intro a ha
    change a = 0
    apply eq_of_weak_ideal_submem hA
    intro J
    have hp : (l J ≫ e.hom) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) := by
      rw [Category.assoc, ← he, hl]
    have hz := congrArg (fun k => (Spec.preimage k).hom a) hp
    simp only [Spec.preimage_comp, Spec.preimage_map, CommRingCat.hom_comp,
      RingHom.comp_apply,
      CommRingCat.hom_ofHom, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero] at hz
    simpa using (Ideal.Quotient.eq_zero_iff_mem.mp hz.symm)
  subst I
  have : IsIso i := by
    rw [he]
    have hq : CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal A)) =
        (RingEquiv.quotientBot A).toCommRingCatIso.inv := by
      ext x
      exact (RingEquiv.quotientBot_symm_mk x).symm
    rw [hq]
    infer_instance
  exact (cancel_epi i).mp (equalizer.condition f g)

/-- For an affine target over `S`, restriction to the quotient spectra is a
bijection on morphisms over `S`. The ordinary spectrum need not belong to the
chosen big fppf site. -/
@[stacks 0AQF "bijectivity"]
public theorem bijective_map_into_affine
    [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D : QuotientSystem B S hS A)
    (fA : Spec (.of A) ⟶ S)
    (hcompat : ∀ J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ fA = D.overS J)
    (X : BigAffineFppf B S hS) :
    Function.Bijective (restrictToFormalSpectrum D fA hcompat
      ((BigAffineFppf.inclusion B S hS).obj X)) := by
  classical
  let Jtop := BigFppfOver.topology B S hS
  have : Jtop.Subcanonical := bigFppfOver_subcanonical B S hS
  have : (Sheaf.sheafifiedYoneda Jtop).Faithful :=
    Sheaf.sheafifiedYoneda_faithful Jtop
  let XS := (BigAffineFppf.toScheme B S hS).obj X
  let e : XS ≅ Spec (.of (affineTargetRing X)) := Scheme.isoSpec XS
  refine ⟨fun f g hfg => ?_, fun φ => ?_⟩
  · apply CostructuredArrow.hom_ext f g
    apply (cancel_mono e.hom).1
    apply hom_eq_of_weak_ideal_quotients hA
      (f.left ≫ e.hom) (g.left ≫ e.hom)
    intro K
    have hk := congrArg
      (fun q => formalSpectrumInclusion D (OrderDual.toDual K) ≫ q)
      hfg
    rw [restrictToFormalSpectrum_spec D fA hcompat
      ((BigAffineFppf.inclusion B S hS).obj X) f K,
      restrictToFormalSpectrum_spec D fA hcompat
      ((BigAffineFppf.inclusion B S hS).obj X) g K] at hk
    exact congrArg (fun z => B.inclusion.map z.left ≫ e.hom)
      ((Sheaf.sheafifiedYoneda Jtop).map_injective hk)
  · let G := Sheaf.sheafifiedYoneda Jtop
    have : G.Full := Sheaf.sheafifiedYoneda_full Jtop
    let m (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
        (BigAffineFppf.inclusion B S hS).obj (D.stage J) ⟶
          (BigAffineFppf.inclusion B S hS).obj X :=
      G.preimage (formalSpectrumInclusion D (OrderDual.toDual J) ≫ φ)
    have hm (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
        G.map (m J) = formalSpectrumInclusion D (OrderDual.toDual J) ≫ φ :=
      Functor.map_preimage G _
    let s (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
        Spec (.of (A ⧸ J.1)) ⟶ Spec (.of (affineTargetRing X)) :=
      B.inclusion.map (m J).left ≫ e.hom
    let f (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
        affineTargetRing X →+* A ⧸ J.1 := (Spec.preimage (s J)).hom
    have hstage (J L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
        (h : J.1 ≤ L.1) :
        (BigAffineFppf.inclusion B S hS).map (D.transition h) ≫ m J = m L := by
      apply G.map_injective
      have hcol :
          G.map ((BigAffineFppf.inclusion B S hS).map (D.transition h)) ≫
            formalSpectrumInclusion D (OrderDual.toDual J) =
          formalSpectrumInclusion D (OrderDual.toDual L) := by
        change (formalSpectrumDiagram D).map (homOfLE h) ≫
          formalSpectrumInclusion D (OrderDual.toDual J) = _
        exact colimit.w (formalSpectrumDiagram D) (homOfLE h)
      rw [Functor.map_comp, hm J, hm L]
      exact (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ φ) hcol)
    have hf (J L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
        (h : J.1 ≤ L.1) :
        (Ideal.Quotient.factor h).comp (f J) = f L := by
      have hs := congrArg (fun k => B.inclusion.map k.left) (hstage J L h)
      change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫
          B.inclusion.map (m J).left = B.inclusion.map (m L).left at hs
      have hs' : Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫ s J = s L := by
        change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor h)) ≫
          (B.inclusion.map (m J).left ≫ e.hom) = _
        exact (Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ e.hom) hs)
      have hp := congrArg Spec.preimage hs'
      have hp' : Spec.preimage (s J) ≫ CommRingCat.ofHom (Ideal.Quotient.factor h) =
          Spec.preimage (s L) := by
        simpa only [Spec.preimage_comp, Spec.preimage_map] using hp
      have hh := congrArg CommRingCat.Hom.hom hp'
      simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] using hh
    let F := lift_compatible_weak_quotient_ring_homs hA f hf
    let q : Spec (.of A) ⟶ XS :=
      Spec.map (CommRingCat.ofHom F) ≫ e.inv
    let fX : XS ⟶ S := ((BigAffineFppf.inclusion B S hS).obj X).hom.hom
    have hquot (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I }) :
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫ q =
          B.inclusion.map (m J).left := by
      change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J.1)) ≫
        (Spec.map (CommRingCat.ofHom F) ≫ e.inv) = _
      rw [← Category.assoc, ← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J.1).comp F)) ≫ e.inv = _
      rw [lift_compatible_weak_quotient_ring_homs_spec hA f hf J]
      change Spec.map (Spec.preimage (s J)) ≫ e.inv = _
      rw [Spec.map_preimage]
      change (B.inclusion.map (m J).left ≫ e.hom) ≫ e.inv = _
      rw [Category.assoc, e.hom_inv_id]
      exact Category.comp_id _
    have hover : q ≫ fX = fA := hom_eq_of_weak_ideal_quotients hA _ _ fun J => by
      rw [← Category.assoc, hquot, hcompat]
      exact congrArg B.inclusion.map (m J).w
    let fOver : (Over.mk fA : Over S) ⟶
        (Over.post B.inclusion).obj ((BigAffineFppf.inclusion B S hS).obj X) :=
      Over.homMk q hover
    refine ⟨fOver, ?_⟩
    apply colimit.hom_ext
    intro J
    change formalSpectrumInclusion D J ≫ _ = _
    refine (restrictToFormalSpectrum_spec D fA hcompat
      ((BigAffineFppf.inclusion B S hS).obj X) fOver J).trans
      (Eq.trans ?_ (hm J))
    exact congrArg G.map (CostructuredArrow.hom_ext _ _ (ObjectProperty.hom_ext _ (hquot J)))

end AlgebraicGeometry.FormalSpace

end
