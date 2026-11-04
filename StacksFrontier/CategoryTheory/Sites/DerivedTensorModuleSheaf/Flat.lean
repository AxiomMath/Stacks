module

public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Monoidal
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.Homology.KFlat.Flat

/-!
# K-flat resolutions of complexes of sheaves of modules over a ring

Let `(C, J)` be a site and `Λ` a commutative ring. Every complex of sheaves of `Λ`-modules on
`C` receives a quasi-isomorphism from a K-flat complex, for the tensor product of
`CategoryTheory.Sheaf.monoidalCategory`; a complex which is bounded above may moreover be
resolved by a K-flat complex with the same bound. This is Stacks 06YS for the category of
sheaves of modules over a ring.

## Main definitions

* `Stacks.ModuleSheaf.sheafifiedFree`: the sheaves which are, up to isomorphism, the
  sheafification of a presheaf of free `Λ`-modules.

## Main results

* `Stacks.ModuleSheaf.preservesFiniteLimits_tensorRight_presheafToSheaf_obj`: the sheafification
  of a presheaf of flat modules is flat: tensoring with it is exact.
* `Stacks.ModuleSheaf.exists_epi_sheafifiedFree`: every sheaf of `Λ`-modules is a quotient of a
  sheafified presheaf of free modules.
* `Stacks.ModuleSheaf.kFlat_of_isStrictlyLE`: a bounded above complex whose terms are sheafified
  presheaves of free modules is K-flat.
* `Stacks.ModuleSheaf.exists_quasiIso_sheafifiedFree_isStrictlyLE`: a complex with cohomology
  vanishing above `a` receives a quasi-isomorphism from a complex whose terms vanish above `a` and
  are sheafified presheaves of free modules.
* `Stacks.ModuleSheaf.exists_kFlat_quasiIso`: every complex of sheaves of `Λ`-modules receives a
  quasi-isomorphism from a K-flat complex.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06XX](https://stacks.math.columbia.edu/tag/06XX)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YR](https://stacks.math.columbia.edu/tag/06YR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe w v u

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory monoidalClosed

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type w) [CommRing Λ] [UnivLE.{max u v, w}]

/-! ### Flatness of sheafified presheaves of flat modules -/

/-- Tensoring a sheaf with the sheafification of a presheaf `P` is sheafifying the objectwise
tensor product of its underlying presheaf with `P`. -/
def tensorRightSheafifyIso (P : Cᵒᵖ ⥤ ModuleCat.{w} Λ) :
    tensorRight ((presheafToSheaf J (ModuleCat.{w} Λ)).obj P) ≅
      sheafToPresheaf J (ModuleCat.{w} Λ) ⋙ tensorRight P ⋙
        presheafToSheaf J (ModuleCat.{w} Λ) :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      (asIso (sheafificationAdjunction J (ModuleCat.{w} Λ)).counit).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.Monoidal.commTensorRight (presheafToSheaf J (ModuleCat.{w} Λ)) P)

omit [UnivLE.{max u v, w}] in
variable {Λ} in
omit [UnivLE.{max u v, w}] in
/-- Tensoring with a presheaf of flat `Λ`-modules is exact on presheaves. -/
theorem preservesFiniteLimits_tensorRight_presheaf (P : Cᵒᵖ ⥤ ModuleCat.{w} Λ)
    (hP : ∀ X, Module.Flat Λ (P.obj X)) : PreservesFiniteLimits (tensorRight P) := by
  apply preservesFiniteLimits_of_evaluation
  intro X
  have : PreservesFiniteLimits (tensorRight (P.obj X)) :=
    (Module.Flat.iff_preservesFiniteLimits_tensorRight (P.obj X)).1 (hP X)
  exact preservesFiniteLimits_of_natIso
    (show (evaluation Cᵒᵖ (ModuleCat.{w} Λ)).obj X ⋙ tensorRight (P.obj X) ≅
        tensorRight P ⋙ (evaluation Cᵒᵖ (ModuleCat.{w} Λ)).obj X from Iso.refl _)

variable {Λ} in
/-- The sheafification of a presheaf of flat `Λ`-modules is flat: tensoring with it is exact. -/
theorem preservesFiniteLimits_tensorRight_presheafToSheaf_obj
    (P : Cᵒᵖ ⥤ ModuleCat.{w} Λ) (hP : ∀ X, Module.Flat Λ (P.obj X)) :
    PreservesFiniteLimits (tensorRight ((presheafToSheaf J (ModuleCat.{w} Λ)).obj P)) := by
  have := preservesFiniteLimits_tensorRight_presheaf P hP
  exact preservesFiniteLimits_of_natIso (tensorRightSheafifyIso J Λ P).symm

/-! ### The resolving class -/

/-- The sheaves of `Λ`-modules which are, up to isomorphism, the sheafification of the presheaf
of free `Λ`-modules `U ↦ Λ[S(U)]` on a presheaf of sets `S`. -/
def sheafifiedFree : ObjectProperty (Sheaf J (ModuleCat.{w} Λ)) := fun F =>
  ∃ S : Cᵒᵖ ⥤ Type w,
    Nonempty ((presheafToSheaf J (ModuleCat.{w} Λ)).obj (S ⋙ ModuleCat.free Λ) ≅ F)

variable {J Λ} in
/-- A sheafified presheaf of free modules is flat: tensoring with it is exact. -/
theorem preservesFiniteLimits_tensorRight_of_sheafifiedFree
    {F : Sheaf J (ModuleCat.{w} Λ)} (hF : sheafifiedFree J Λ F) :
    PreservesFiniteLimits (tensorRight F) := by
  obtain ⟨S, ⟨e⟩⟩ := hF
  have := preservesFiniteLimits_tensorRight_presheafToSheaf_obj J (S ⋙ ModuleCat.free Λ)
    (fun X => inferInstanceAs (Module.Flat Λ (S.obj X →₀ Λ)))
  exact preservesFiniteLimits_of_natIso
    (NatIso.ofComponents (fun G => whiskerLeftIso G e) (fun f => (whisker_exchange f e.hom).symm) :
      tensorRight ((presheafToSheaf J (ModuleCat.{w} Λ)).obj (S ⋙ ModuleCat.free Λ)) ≅
        tensorRight F)

/-- The class `sheafifiedFree J Λ` is closed under isomorphisms. -/
instance sheafifiedFree_isClosedUnderIsomorphisms :
    (sheafifiedFree J Λ).IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨S, ⟨e'⟩⟩ => ⟨S, ⟨e' ≪≫ e⟩⟩

/-- The class `sheafifiedFree J Λ` contains a zero object. -/
instance sheafifiedFree_containsZero : (sheafifiedFree J Λ).ContainsZero where
  exists_zero := by
    let S : Cᵒᵖ ⥤ Type w := (Functor.const _).obj PEmpty
    have hP : IsZero (S ⋙ ModuleCat.free Λ) := Functor.isZero _ (fun _ =>
      @ModuleCat.isZero_of_subsingleton _ _ ((ModuleCat.free Λ).obj PEmpty)
        (inferInstanceAs (Subsingleton (PEmpty →₀ Λ))))
    exact ⟨_, Functor.map_isZero _ hP, ⟨S, ⟨Iso.refl _⟩⟩⟩

variable {J Λ} in
/-- The class `sheafifiedFree J Λ` is closed under binary biproducts. -/
theorem sheafifiedFree_biprod {F G : Sheaf J (ModuleCat.{w} Λ)}
    (hF : sheafifiedFree J Λ F) (hG : sheafifiedFree J Λ G) : sheafifiedFree J Λ (F ⊞ G) := by
  obtain ⟨S, ⟨e⟩⟩ := hF
  obtain ⟨T, ⟨e'⟩⟩ := hG
  let Φ := (Functor.whiskeringRight Cᵒᵖ _ _).obj (ModuleCat.free.{w} Λ)
  have : PreservesColimitsOfShape (Discrete WalkingPair) Φ := by
    have := (ModuleCat.adj.{w} Λ).leftAdjoint_preservesColimits
    infer_instance
  let e₁ : Φ.obj (S ⨿ T) ≅ Φ.obj S ⊞ Φ.obj T :=
    (PreservesColimitPair.iso Φ S T).symm ≪≫ (biprod.isoCoprod _ _).symm
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint
    (presheafToSheaf J (ModuleCat.{w} Λ))
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (presheafToSheaf J (ModuleCat.{w} Λ))
  exact ⟨S ⨿ T, ⟨(presheafToSheaf J _).mapIso e₁ ≪≫ (presheafToSheaf J _).mapBiprod _ _ ≪≫
    biprod.mapIso e e'⟩⟩

/-- Every sheaf of `Λ`-modules is a quotient of a sheafified presheaf of free modules. -/
theorem exists_epi_sheafifiedFree (F : Sheaf J (ModuleCat.{w} Λ)) :
    ∃ (G : Sheaf J (ModuleCat.{w} Λ)) (_ : sheafifiedFree J Λ G) (p : G ⟶ F), Epi p := by
  let S : Cᵒᵖ ⥤ Type w := F.val ⋙ forget (ModuleCat.{w} Λ)
  let ε : S ⋙ ModuleCat.free Λ ⟶ F.val :=
    Functor.whiskerLeft F.val (ModuleCat.adj Λ).counit
  have : ∀ X, Epi (ε.app X) := fun X =>
    (ModuleCat.epi_iff_surjective _).2 (fun x => ⟨ModuleCat.freeMk x, by
      simp [ε, ModuleCat.adj]⟩)
  have : Epi ε := NatTrans.epi_of_epi_app _
  exact ⟨(presheafToSheaf J _).obj (S ⋙ ModuleCat.free Λ), ⟨S, ⟨Iso.refl _⟩⟩,
    (presheafToSheaf J _).map ε ≫ (sheafificationAdjunction J _).counit.app F, inferInstance⟩

/-! ### K-flat complexes and resolutions -/

section Resolutions

open CochainComplex.KFlatBifunctor

variable {J Λ}

/-- A sheafified presheaf of free modules placed in a single degree is a K-flat complex. -/
theorem kFlat_single_of_sheafifiedFree {M : Sheaf J (ModuleCat.{w} Λ)}
    (hM : sheafifiedFree J Λ M) (q : ℤ) :
    KFlat (curriedTensor (Sheaf J (ModuleCat.{w} Λ)))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj M) := by
  have := preservesFiniteLimits_tensorRight_of_sheafifiedFree hM
  exact kFlat_single_of_exact (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) M q
    (fun G hG => HomologicalComplex.Acyclic.map (tensorRight M) hG)

/-- A sequential colimit of acyclic complexes of sheaves of modules is acyclic. -/
theorem acyclic_of_isColimit_nat
    (E : ℕ ⥤ CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) (s : Cocone E)
    (hs : IsColimit s) (hE : ∀ i, (E.obj i).Acyclic) : s.pt.Acyclic := fun n =>
  (CochainComplex.KFlat.acyclic_colimit E hE n).of_iso
    ((colimit.isColimit E).coconePointUniqueUpToIso hs)

/-- A bounded above complex of sheafified presheaves of free modules is K-flat (Stacks 06YQ). -/
theorem kFlat_of_isStrictlyLE (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) (b : ℤ)
    [K.IsStrictlyLE b] (hK : ∀ n, sheafifiedFree J Λ (K.X n)) :
    KFlat (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) K :=
  CochainComplex.KFlatBifunctor.kFlat_of_isStrictlyLE _ K b
    (fun _ ↦ inferInstance)
    (acyclic_of_isColimit_nat (J := J) (Λ := Λ))
    (fun q => kFlat_single_of_sheafifiedFree (hK q) q)

/-- A complex with cohomology vanishing above `a` receives a quasi-isomorphism from a complex of
sheafified presheaves of free modules vanishing above `a` (Stacks 05T7). -/
theorem exists_quasiIso_sheafifiedFree_isStrictlyLE
    (K : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) (a : ℤ) [K.IsLE a] :
    ∃ (L : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) (f : L ⟶ K),
      QuasiIso f ∧ (∀ n, sheafifiedFree J Λ (L.X n)) ∧ L.IsStrictlyLE a := by
  obtain ⟨L, f, hf, hL, hLE⟩ :=
    (CochainComplex.exists_quasiIso_prop (sheafifiedFree J Λ) (exists_epi_sheafifiedFree J Λ)
      a).2 K
  exact ⟨L, f, hf, hL, hLE⟩

/-- Every complex of sheaves of `Λ`-modules receives a quasi-isomorphism from a K-flat complex
(Stacks 06YS). -/
theorem exists_kFlat_quasiIso (G : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) :
    ∃ (P : CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ) (f : P ⟶ G),
      KFlat (curriedTensor (Sheaf J (ModuleCat.{w} Λ))) P ∧ QuasiIso f := by
  obtain ⟨Q, q, g, hq, hle, hfree, -, hladder⟩ :=
    StacksDraft.UnboundedLeftDerivedFunctor.exists_sequence_quasiIso_truncLE (sheafifiedFree J Λ)
      (fun _ _ => sheafifiedFree_biprod) (exists_epi_sheafifiedFree J Λ) G
  let D := Functor.ofSequence g
  let s : Cocone D := Cocone.mk G
    (NatTrans.ofSequence (fun n ↦ q n ≫ G.ιTruncLE (n : ℤ)) (fun n ↦ by
      rw [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map]
      exact (hladder n).trans (Category.comp_id _).symm))
  refine ⟨colimit D, (colimit.isColimit D).desc s, ?_,
    StacksDraft.UnboundedLeftDerivedFunctor.quasiIso_of_isColimit_of_quasiIso_truncLE q hq
      (colimit.isColimit D) _ (fun n => (colimit.isColimit D).fac s n)⟩
  refine CochainComplex.KFlatBifunctor.kFlat_of_isColimit _ (colimit.cocone D)
    (colimit.isColimit _) (fun _ ↦ inferInstance)
    (acyclic_of_isColimit_nat (J := J) (Λ := Λ)) (fun n ↦ ?_)
  have : (D.obj n).IsStrictlyLE n := hle n
  exact kFlat_of_isStrictlyLE (D.obj n) n (hfree n)

end Resolutions

end Stacks.ModuleSheaf
