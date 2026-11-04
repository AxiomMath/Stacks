module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafComplexLocalHom
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Monoidal.FunctorCategoryConst
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Transport
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorBoundedAbove
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.TotalComplexTransport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived tensor product of constant sheaves

Let `(C, J)` be a site and `Λ` a commutative ring. The constant sheaf functor
`M ↦ M̲` from `Λ`-modules to sheaves of `Λ`-modules is exact, commutes with colimits and is
monoidal, and it carries free modules to sheafified presheaves of free modules. Consequently, for
bounded above complexes `P` and `P'` of finite free `Λ`-modules,

`Hⁿ(P̲ ⊗_Λ^L P̲') ≅ Hⁿ(P ⊗_Λ P')̲`.

If `Λ` is Noetherian, every bounded complex of finitely generated modules is quasi-isomorphic
to such a complex (Stacks 066E and 064U), so for bounded complexes `M`, `N` of finitely generated
modules the cohomology sheaves of `M̲ ⊗_Λ^L N̲` are constant sheaves on finitely generated
modules.

## Main results

* `Stacks.ModuleSheaf.sheafifiedFree_constantSheaf_obj`: the constant sheaf on a free module is a
  sheafified presheaf of free modules.
* `Stacks.ModuleSheaf.nonempty_homology_constantSheaf_tensor_iso`: the computation for finite
  free complexes.
* `Stacks.ModuleSheaf.exists_homology_constantSheaf_tensor_iso`: for bounded complexes of finitely
  generated modules over a Noetherian ring, the cohomology sheaves of the derived tensor product
  are constant on finitely generated modules.

## References

* [Stacks Project, Tag 094H](https://stacks.math.columbia.edu/tag/094H)
* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CochainComplex.KFlatBifunctor

universe w v u

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory monoidalClosed
  CochainComplex.braidedCategory derivedMonoidal HasDerivedCategory.standard

/-! ### Finitely generated modules -/

section Modules

variable {Λ : Type w} [CommRing Λ]

/-- The modules finitely generated over `Λ` are closed under finite coproducts. -/
theorem isClosedUnderFiniteCoproducts_finite :
    ObjectProperty.IsClosedUnderFiniteCoproducts
      (fun M : ModuleCat.{w} Λ => Module.Finite Λ M) := by
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (fun M : ModuleCat.{w} Λ => Module.Finite Λ M) :=
    ⟨fun e h => Module.Finite.equiv e.toLinearEquiv⟩
  have : ObjectProperty.IsClosedUnderBinaryCoproducts
      (fun M : ModuleCat.{w} Λ => Module.Finite Λ M) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.mk' (fun _ ⟨F, hF⟩ => by
      have := hF ⟨.left⟩
      have := hF ⟨.right⟩
      have : Module.Finite Λ (ModuleCat.of Λ (F.obj ⟨.left⟩ × F.obj ⟨.right⟩)) :=
        inferInstanceAs (Module.Finite Λ (F.obj ⟨.left⟩ × F.obj ⟨.right⟩))
      exact Module.Finite.equiv (HasColimit.isoOfNatIso (diagramIsoPair F) ≪≫
        (biprod.isoCoprod _ _).symm ≪≫ ModuleCat.biprodIsoProd _ _).symm.toLinearEquiv)
  have : ObjectProperty.ContainsZero (fun M : ModuleCat.{w} Λ => Module.Finite Λ M) :=
    ⟨⟨ModuleCat.of Λ PUnit, ModuleCat.isZero_of_subsingleton _,
      inferInstanceAs (Module.Finite Λ PUnit)⟩⟩
  exact ObjectProperty.IsClosedUnderFiniteCoproducts.mk'

variable [IsNoetherianRing Λ]

/-- **A bounded complex of finitely generated modules over a Noetherian ring is quasi-isomorphic
to a bounded above complex of finite free modules** with the same upper bound. -/
@[sga "5 VIII 5.1" "special case", sga "6 I 5.0" "more general"]
theorem exists_finiteFree_isStrictlyLE_iso (M : CochainComplex (ModuleCat.{w} Λ) ℤ) (a b : ℤ)
    (hM : ∀ n, n ∉ Set.Icc a b → IsZero (M.X n)) (hfg : ∀ n, ModuleCat.isFG Λ (M.X n)) :
    ∃ P : CochainComplex (ModuleCat.{w} Λ) ℤ, P.IsStrictlyLE b ∧
      (∀ i, Module.Finite Λ (P.X i) ∧ Module.Free Λ (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj M) := by
  have hle : M.IsStrictlyLE b :=
    (CochainComplex.isStrictlyLE_iff M b).2 fun n hn => hM n (by simp only [Set.mem_Icc]; omega)
  have hQle : (DerivedCategory.Q.obj M).IsLE b :=
    (DerivedCategory.isLE_Q_obj_iff M b).2 inferInstance
  have hvan : ∀ i, b < i → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{w} Λ) i).obj (DerivedCategory.Q.obj M)) :=
    fun i hi => DerivedCategory.isZero_of_isLE _ b i hi
  have hfin : ∀ i, Module.Finite Λ
      ((DerivedCategory.homologyFunctor (ModuleCat.{w} Λ) i).obj (DerivedCategory.Q.obj M)) := by
    intro i
    have : Module.Finite Λ (M.X i) := (ModuleCat.isFG_iff _).1 (hfg i)
    have := StacksDraft.PseudoCoherence.finite_homology_of_finite_X M i
    exact Module.Finite.equiv
      ((DerivedCategory.homologyFunctorFactors _ i).app M).symm.toLinearEquiv
  have hK : StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj M) :=
    ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      (DerivedCategory.Q.obj M) 0 Λ).2.1).2 ⟨⟨b, hvan⟩, hfin⟩
  obtain ⟨P, α, hP, hPle, hα⟩ :=
    StacksDraft.PseudoCoherence.exists_finiteFree_representative_le _ b hK hvan
  exact ⟨P, hPle, hP, ⟨asIso α⟩⟩

end Modules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type w) [CommRing Λ] [UnivLE.{max u v, w}]

/-! ### The constant sheaf functor -/

/-- The constant sheaf functor commutes with small colimits. -/
instance preservesColimitsOfSize_constantSheaf :
    PreservesColimitsOfSize.{0, 0} (constantSheaf J (ModuleCat.{w} Λ)) :=
  inferInstanceAs (PreservesColimitsOfSize.{0, 0}
    (Functor.const Cᵒᵖ ⋙ presheafToSheaf J (ModuleCat.{w} Λ)))

/-- The constant sheaf functor is right exact. -/
instance preservesFiniteColimits_constantSheaf :
    PreservesFiniteColimits (constantSheaf J (ModuleCat.{w} Λ)) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- The constant sheaf functor is left exact. -/
instance preservesFiniteLimits_constantSheaf :
    PreservesFiniteLimits (constantSheaf J (ModuleCat.{w} Λ)) :=
  inferInstanceAs (PreservesFiniteLimits (Functor.const Cᵒᵖ ⋙ presheafToSheaf J (ModuleCat.{w} Λ)))

/-- The constant sheaf functor is monoidal. -/
@[instance_reducible]
def constantSheafMonoidal : (constantSheaf J (ModuleCat.{w} Λ)).Monoidal :=
  inferInstanceAs ((Functor.const Cᵒᵖ ⋙ presheafToSheaf J (ModuleCat.{w} Λ)).Monoidal)

variable {Λ} in
/-- The constant sheaf on a free module is the sheafification of a presheaf of free modules. -/
theorem sheafifiedFree_constantSheaf_obj (M : ModuleCat.{w} Λ) [Module.Free Λ M] :
    sheafifiedFree J Λ ((constantSheaf J (ModuleCat.{w} Λ)).obj M) := by
  let ι := Module.Free.ChooseBasisIndex Λ M
  let e : M ≅ (ModuleCat.free Λ).obj ι := (Module.Free.chooseBasis Λ M).repr.toModuleIso
  exact ⟨(Functor.const Cᵒᵖ).obj ι, ⟨(presheafToSheaf J (ModuleCat.{w} Λ)).mapIso
    (NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp) :
      (Functor.const Cᵒᵖ).obj ι ⋙ ModuleCat.free Λ ≅
        (Functor.const Cᵒᵖ).obj ((ModuleCat.free Λ).obj ι)) ≪≫
      (constantSheaf J (ModuleCat.{w} Λ)).mapIso e.symm⟩⟩

/-! ### The computation for finite free complexes -/

variable {J Λ}

/-- **The derived tensor product of the constant sheaves on two bounded above complexes of
finite free modules** has as cohomology sheaves the constant sheaves on the cohomology of the
tensor product of the two complexes. -/
theorem nonempty_homology_constantSheaf_tensor_iso (P P' : CochainComplex (ModuleCat.{w} Λ) ℤ)
    (a b : ℤ) [P.IsStrictlyLE a] [P'.IsStrictlyLE b] (hP : ∀ i, Module.Free Λ (P.X i))
    (hP' : ∀ i, Module.Free Λ (P'.X i)) (n : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor _ n).obj
        (DerivedCategory.Q.obj (((constantSheaf J (ModuleCat.{w} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P) ⊗
          DerivedCategory.Q.obj (((constantSheaf J (ModuleCat.{w} Λ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj P')) ≅
      (constantSheaf J (ModuleCat.{w} Λ)).obj ((P ⊗ P').homology n)) := by
  let := constantSheafMonoidal J Λ
  let c := constantSheaf J (ModuleCat.{w} Λ)
  have hcP := isStrictlyLE_mapHomologicalComplex c P a
  have hcP' := isStrictlyLE_mapHomologicalComplex c P' b
  have hf : ∀ Q : CochainComplex (ModuleCat.{w} Λ) ℤ, (∀ i, Module.Free Λ (Q.X i)) →
      ∀ i, sheafifiedFree J Λ ((c.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q |>.X i) :=
    fun Q hQ i => have := hQ i; sheafifiedFree_constantSheaf_obj J (Q.X i)
  let T : (c.mapHomologicalComplex (ComplexShape.up ℤ)).obj (P ⊗ P') ≅
      (c.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⊗
        (c.mapHomologicalComplex (ComplexShape.up ℤ)).obj P' :=
    Functor.mapBifunctorTotalIso (curriedTensor _) (curriedTensor _) c c c
      (fun M N => (Functor.Monoidal.μIso c M N).symm)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (fun f N => by simp) (fun M _ _ g => by simp) P P'
  exact ⟨(DerivedCategory.homologyFunctor _ n).mapIso
      ((derivedTensorIso (kFlat_of_isStrictlyLE _ a (hf P hP))
          (kFlat_of_isStrictlyLE _ b (hf P' hP'))) ≪≫
        DerivedCategory.Q.mapIso T.symm) ≪≫
    (DerivedCategory.homologyFunctorFactors _ n).app _ ≪≫
    (c.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).app (P ⊗ P')⟩

/-! ### Bounded complexes of finitely generated modules over a Noetherian ring -/

variable [IsNoetherianRing Λ]

/-- **The cohomology sheaves of the derived tensor product of the constant sheaves on two bounded
complexes of finitely generated modules over a Noetherian ring are constant sheaves on finitely
generated modules.** -/
theorem exists_homology_constantSheaf_tensor_iso (M N : CochainComplex (ModuleCat.{w} Λ) ℤ)
    (a b a' b' : ℤ) (hM : ∀ n, n ∉ Set.Icc a b → IsZero (M.X n))
    (hMfg : ∀ n, ModuleCat.isFG Λ (M.X n)) (hN : ∀ n, n ∉ Set.Icc a' b' → IsZero (N.X n))
    (hNfg : ∀ n, ModuleCat.isFG Λ (N.X n)) (n : ℤ) :
    ∃ E : ModuleCat.{w} Λ, ModuleCat.isFG Λ E ∧
      Nonempty ((DerivedCategory.homologyFunctor _ n).obj
          (DerivedCategory.Q.obj (((constantSheaf J (ModuleCat.{w} Λ)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj M) ⊗
            DerivedCategory.Q.obj (((constantSheaf J (ModuleCat.{w} Λ)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj N)) ≅
        (constantSheaf J (ModuleCat.{w} Λ)).obj E) := by
  let c := constantSheaf J (ModuleCat.{w} Λ)
  obtain ⟨P, hP, hPf, ⟨e⟩⟩ := exists_finiteFree_isStrictlyLE_iso M a b hM hMfg
  obtain ⟨P', hP', hP'f, ⟨e'⟩⟩ := exists_finiteFree_isStrictlyLE_iso N a' b' hN hNfg
  have hfinite : Module.Finite Λ ((P ⊗ P').X n) := by
    have := isClosedUnderFiniteCoproducts_finite (Λ := Λ)
    exact Stacks.ConstantSheaf.prop_mapBifunctor_of_isStrictlyLE (curriedTensor _) P P' b b'
      (fun M : ModuleCat.{w} Λ => Module.Finite Λ M)
      (fun p q => by
        have := (hPf p).1
        have := (hP'f q).1
        exact inferInstanceAs (Module.Finite Λ (TensorProduct Λ (P.X p) (P'.X q)))) n
  let r : ∀ (X Y : CochainComplex (ModuleCat.{w} Λ) ℤ),
      (DerivedCategory.Q.obj X ≅ DerivedCategory.Q.obj Y) →
        (DerivedCategory.Q.obj ((c.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≅
          DerivedCategory.Q.obj ((c.mapHomologicalComplex (ComplexShape.up ℤ)).obj Y)) :=
    fun X Y f => (c.mapDerivedCategoryFactors.app X).symm ≪≫ c.mapDerivedCategory.mapIso f ≪≫
      c.mapDerivedCategoryFactors.app Y
  obtain ⟨T⟩ := nonempty_homology_constantSheaf_tensor_iso (J := J) P P' b b'
    (fun i => (hPf i).2) (fun i => (hP'f i).2) n
  exact ⟨(P ⊗ P').homology n, (ModuleCat.isFG_iff _).2
    (StacksDraft.PseudoCoherence.finite_homology_of_finite_X (P ⊗ P') n),
    ⟨(DerivedCategory.homologyFunctor _ n).mapIso (r _ _ e.symm ⊗ᵢ r _ _ e'.symm) ≪≫ T⟩⟩

end Stacks.ModuleSheaf
