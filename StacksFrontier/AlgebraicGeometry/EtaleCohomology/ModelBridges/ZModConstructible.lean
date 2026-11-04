module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.ConstantSheafSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Fiber
public import StacksFrontier.Topology.Sheaves.Modules.TensorExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IteratedRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TrivialityAndGlobalSections
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs
public import StacksFrontier.CategoryTheory.Sites.Point.StalkLeftAdjoint
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CurveConstantCoefficientsUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.UnderlyingTower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimitCategory
public import StacksFrontier.CategoryTheory.Sites.PullbackSheafCompose

/-!
# Constructibility of sheaves of `ℤ/nℤ`-modules from their underlying abelian sheaves

A sheaf of `ℤ/nℤ`-modules on the small étale site is a constructible sheaf of modules as soon as
its underlying sheaf of abelian groups is a constructible abelian sheaf. The two notions of
[Stacks, Tag 03RW] (parts (2) and (3)) differ only in the local constant values: a finite abelian
group, respectively a finitely generated module. The point is that forgetting the
`ℤ/nℤ`-module structure is fully faithful, since an additive map of modules annihilated by `n`
is `ℤ/nℤ`-linear.

## Main results

* `Stacks.ConstantSheaf.exists_constantSheaf_iso_of_constantSheaf_iso_forget`: on a site with a
  final object, a sheaf of `ℤ/nℤ`-modules whose underlying abelian sheaf is the constant sheaf
  of an abelian group `A` is the constant sheaf of the `ℤ/nℤ`-module `A/nA`.
* `Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_isFiniteLocallyConstant_forget`: a sheaf
  of `ℤ/nℤ`-modules whose underlying abelian sheaf is finite locally constant is locally constant
  with finitely generated values.
* `AlgebraicGeometry.isConstructibleModuleSheaf_zmod_of_isConstructibleAbelianSheaf`: the same
  for constructibility on the small étale site of Tag 021B.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_zmod_of_isConstructibleEtaleAbelianSheaf`:
  the same in the model `EtaleModules (ZMod n) X`.

## Implementation notes

The local value is `A/nA` rather than `A` itself: the constant sheaf of `A` on an empty object of
the site is zero whatever `A` is, so `A` need not be annihilated by `n`. The constant sheaf of the
quotient map `A ⟶ A/nA` is an epimorphism (a left adjoint preserves epimorphisms) and a split
monomorphism (it is the first factor of the given isomorphism, the second factor existing because
the sections of the target are annihilated by `n`), hence an isomorphism.

Inverse image along a stratum commutes with forgetting the module structure by
`CategoryTheory.Functor.sheafPullbackSheafComposeIso`, and the passage between Mathlib's small
étale site and the site of Tag 021B is restriction along the dense subsite inclusion, which
commutes with forgetting on the nose.

## References

* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe w v u r

namespace Stacks.ConstantSheaf

/-- Forgetting the `ℤ/nℤ`-module structure is a left adjoint: it is restriction of scalars along
`ℤ ⟶ ℤ/nℤ`, a left adjoint, followed by the equivalence of `ℤ`-modules with abelian groups. -/
theorem forget₂_zmod_isLeftAdjoint (n : ℕ) :
    (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w}).IsLeftAdjoint := by
  show (ModuleCat.restrictScalars (Int.castRingHom (ZMod n)) ⋙
    forget₂ (ModuleCat ℤ) AddCommGrpCat).IsLeftAdjoint
  infer_instance

/-- Forgetting the `ℤ/nℤ`-module structure preserves sheafification, on any site, being a left
adjoint. -/
theorem preservesSheafification_forget₂_zmod {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (n : ℕ) :
    J.PreservesSheafification (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w}) :=
  have := forget₂_zmod_isLeftAdjoint.{w} n
  Sheaf.preservesSheafification_of_adjunction J
    (Adjunction.ofIsLeftAdjoint (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w}))

section ConstantValue

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)
  (n : ℕ) [HasWeakSheafify K AddCommGrpCat.{w}] [HasWeakSheafify K (ModuleCat.{w} (ZMod n))]
  [K.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})]
  [K.PreservesSheafification (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})]

/-- **A sheaf of `ℤ/nℤ`-modules whose underlying abelian sheaf is constant is constant.** On a
site with a final object, if the underlying abelian sheaf of `M` is the constant sheaf of an
abelian group `A`, then `M` is the constant sheaf of the `ℤ/nℤ`-module `A/nA`, which is finite
when `A` is. -/
theorem exists_constantSheaf_iso_of_constantSheaf_iso_forget {T : C} (hT : IsTerminal T)
    (A : AddCommGrpCat.{w}) (M : Sheaf K (ModuleCat.{w} (ZMod n)))
    (φ : (constantSheaf K AddCommGrpCat.{w}).obj A ≅
      (sheafCompose K (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).obj M) :
    ∃ E : ModuleCat.{w} (ZMod n), (Finite A → Finite E) ∧
      Nonempty ((constantSheaf K (ModuleCat.{w} (ZMod n))).obj E ≅ M) := by
  let Fg := forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w}
  let M' := (sheafCompose K Fg).obj M
  let adj := constantSheafAdj K AddCommGrpCat.{w} hT
  let f₀ : A ⟶ A := n • 𝟙 A
  let Q : AddCommGrpCat.{w} := cokernel f₀
  let π : A ⟶ Q := cokernel.π f₀
  have hsurj : Function.Surjective π := (AddCommGrpCat.epi_iff_surjective π).1 inferInstance
  have hQ : ∀ x : Q, n • x = 0 := by
    intro x
    obtain ⟨a, rfl⟩ := hsurj x
    have h := ConcreteCategory.congr_hom (cokernel.condition f₀) a
    rw [ConcreteCategory.comp_apply] at h
    rwa [← map_nsmul]
  let : Module (ZMod n) Q := AddCommGroup.zmodModule hQ
  let E : ModuleCat.{w} (ZMod n) := ModuleCat.of (ZMod n) Q
  let a : A ⟶ M'.obj.obj (op T) := adj.homEquiv A M' φ.hom
  have ha : f₀ ≫ a = 0 := by
    ext x
    show a (n • x) = 0
    rw [map_nsmul]
    exact ZModModule.char_nsmul_eq_zero n (show M.obj.obj (op T) from a x)
  let a' : Q ⟶ M'.obj.obj (op T) := cokernel.desc _ a ha
  let ψ : (constantSheaf K AddCommGrpCat.{w}).obj Q ⟶ M' := (adj.homEquiv _ M').symm a'
  let g := (constantSheaf K AddCommGrpCat.{w}).map π
  have hfac : g ≫ ψ = φ.hom := by
    rw [← Adjunction.homEquiv_naturality_left_symm, cokernel.π_desc]
    exact (adj.homEquiv A M').symm_apply_apply φ.hom
  have : IsSplitMono g :=
    IsSplitMono.mk' ⟨ψ ≫ φ.inv, by rw [← Category.assoc, hfac, Iso.hom_inv_id]⟩
  have : (constantSheaf K AddCommGrpCat.{w}).IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
  have : Epi g := (constantSheaf K AddCommGrpCat.{w}).map_epi π
  have : IsIso g := isIso_of_epi_of_isSplitMono g
  have : IsIso ψ := by
    rw [show ψ = inv g ≫ φ.hom by rw [← hfac, IsIso.inv_hom_id_assoc]]
    infer_instance
  have := Stacks.EtaleCohomology.forget₂_zmod_full.{w} n
  exact ⟨E, fun _ => Finite.of_surjective _ hsurj, ⟨(sheafCompose K Fg).preimageIso
    ((constantCommuteCompose K Fg).app E ≪≫ asIso ψ)⟩⟩

end ConstantValue

section LocallyConstant

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (n : ℕ)
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} (ZMod n))]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})]
  [∀ V : C, (J.over V).HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})]

/-- **Finite local constancy of the underlying abelian sheaf gives local constancy of finite
type.** A sheaf of `ℤ/nℤ`-modules whose underlying abelian sheaf is finite locally constant is
locally constant with finitely generated values, on the same trivializing coverings.

`Stacks.ConstantSheaf.isFiniteLocallyConstant_moduleSheaf_iff_forget₂` gives this for `n ≠ 0`
on sites with coefficients in the universe of their objects; the statement here has neither
restriction, which is what the coefficient universe `max (u + 1) r` of the small étale site
needs. -/
theorem isFiniteTypeLocallyConstant_of_isFiniteLocallyConstant_forget
    (M : Sheaf J (ModuleCat.{w} (ZMod n)))
    (hM : IsFiniteLocallyConstant J
      ((sheafCompose J (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).obj M)) :
    IsFiniteTypeLocallyConstant (ZMod n) J M := by
  intro U
  obtain ⟨I, V, f, hf, h⟩ := hM.exists_finite_cover U
  refine ⟨I, V, f, hf, fun i => ?_⟩
  obtain ⟨A, hA, ⟨φ⟩⟩ := h i
  have := preservesSheafification_forget₂_zmod.{w} (J.over (V i)) n
  obtain ⟨E, hE, ⟨e⟩⟩ := exists_constantSheaf_iso_of_constantSheaf_iso_forget (J.over (V i)) n
    (Over.mkIdTerminal (X := V i)) A ((J.overPullback (ModuleCat.{w} (ZMod n)) (V i)).obj M) φ
  have := hE hA
  exact ⟨E, (ModuleCat.isFG_iff _).2 (Module.Finite.of_finite (R := ZMod n)), ⟨e⟩⟩

end LocallyConstant

end Stacks.ConstantSheaf

namespace AlgebraicGeometry

attribute [local instance] SmallEtale.isRightAdjointPushforward_moduleCat
  SmallEtale.hasWeakSheafifyOver_moduleCat

variable (B : BigEtaleSite.{u}) (n : ℕ)

/-- **Inverse image along small étale base change commutes with forgetting the `ℤ/nℤ`-module
structure**: `CategoryTheory.Functor.sheafPullbackSheafComposeIso` at the forgetful functor, which
preserves all colimits and sheafification. -/
def smallEtaleZModPullbackForgetIso {S T : B.Scheme} (g : T ⟶ S)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{max (u + 1) r} (ZMod n))) :
    ((smallEtaleBaseChange B g).sheafPullback AddCommGrpCat.{max (u + 1) r}
        (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)).obj
        ((sheafCompose _
          (forget₂ (ModuleCat.{max (u + 1) r} (ZMod n)) AddCommGrpCat.{max (u + 1) r})).obj F) ≅
      (sheafCompose _
          (forget₂ (ModuleCat.{max (u + 1) r} (ZMod n)) AddCommGrpCat.{max (u + 1) r})).obj
        (((smallEtaleBaseChange B g).sheafPullback (ModuleCat.{max (u + 1) r} (ZMod n))
          (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).obj F) :=
  let Φ := smallEtaleBaseChange B g
  let _ : ∀ P : (SmallEtale B S.obj S.property)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) r},
      Φ.op.HasPointwiseLeftKanExtension P := fun _ Y => by
    let _ := hasColimitsOfShape_of_essentiallySmall.{u + 1}
      (CostructuredArrow Φ.op Y) AddCommGrpCat.{max (u + 1) r}
    infer_instance
  let _ : ∀ P : (SmallEtale B S.obj S.property)ᵒᵖ ⥤ ModuleCat.{max (u + 1) r} (ZMod n),
      Φ.op.HasPointwiseLeftKanExtension P := fun _ Y => by
    let _ := hasColimitsOfShape_of_essentiallySmall.{u + 1}
      (CostructuredArrow Φ.op Y) (ModuleCat.{max (u + 1) r} (ZMod n))
    infer_instance
  let _ : ∀ Y : (SmallEtale B T.obj T.property)ᵒᵖ,
      PreservesColimitsOfShape (CostructuredArrow Φ.op Y)
        (forget₂ (ModuleCat.{max (u + 1) r} (ZMod n)) AddCommGrpCat.{max (u + 1) r}) := fun Y => by
    have := Stacks.ConstantSheaf.forget₂_zmod_isLeftAdjoint.{max (u + 1) r} n
    infer_instance
  have := Stacks.ConstantSheaf.preservesSheafification_forget₂_zmod.{max (u + 1) r}
    (SmallEtale.topology B T.obj T.property) n
  Φ.sheafPullbackSheafComposeIso (ModuleCat.{max (u + 1) r} (ZMod n))
    (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)
    (forget₂ (ModuleCat.{max (u + 1) r} (ZMod n)) AddCommGrpCat.{max (u + 1) r}) F

/-- **A sheaf of `ℤ/nℤ`-modules with constructible underlying abelian sheaf is constructible**
([Stacks, Tag 03RW], parts (2) and (3)), on the small étale site of Tag 021B: on every stratum
the inverse image of the underlying abelian sheaf is finite locally constant, it is the
underlying abelian sheaf of the inverse image, and that is then locally constant with finitely
generated values. -/
theorem isConstructibleModuleSheaf_zmod_of_isConstructibleAbelianSheaf (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} (ZMod n)))
    (hF : IsConstructibleAbelianSheaf B X
      ((sheafCompose _
        (forget₂ (ModuleCat.{max (u + 1) r} (ZMod n)) AddCommGrpCat.{max (u + 1) r})).obj F)) :
    IsConstructibleModuleSheaf B X (ZMod n) F := by
  have : ∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      ((SmallEtale.topology B T.obj T.property).over V).PreservesSheafification
        (forget₂ (ModuleCat.{max (u + 1) r} (ZMod n)) AddCommGrpCat.{max (u + 1) r}) :=
    fun T V => Stacks.ConstantSheaf.preservesSheafification_forget₂_zmod.{max (u + 1) r}
      ((SmallEtale.topology B T.obj T.property).over V) n
  intro U
  obtain ⟨s, hs⟩ := hF U
  exact ⟨s, fun i =>
    Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_of_isFiniteLocallyConstant_forget.{
      max (u + 1) r} _ n _ (Stacks.ConstantSheaf.IsFiniteLocallyConstant.of_iso _
        (smallEtaleZModPullbackForgetIso B n (s.inclusion i) F) (hs i))⟩

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

/-- **A sheaf of `ℤ/nℤ`-modules with constructible underlying abelian sheaf is constructible**,
in the model `EtaleModules (ZMod n) X` ([Stacks, Tag 03RW], parts (2) and (3)). The transport to
the small étale site of Tag 021B is restriction along the dense subsite inclusion, which commutes
with forgetting the module structure on the nose. -/
theorem isConstructibleEtaleModule_zmod_of_isConstructibleEtaleAbelianSheaf (n : ℕ)
    {X : Scheme.{u}} (F : EtaleModules.{u, 0} (ZMod n) X)
    (hF : _root_.Stacks.EtaleCohomology.IsConstructibleSmallEtaleAbelianSheaf.{u, 0}
      ((_root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, 0} (ZMod n) X).obj F)) :
    IsConstructibleEtaleModule (ZMod n) F :=
  AlgebraicGeometry.isConstructibleModuleSheaf_zmod_of_isConstructibleAbelianSheaf.{u, 0} _ n _ _ hF

end Stacks.EtaleCohomology
