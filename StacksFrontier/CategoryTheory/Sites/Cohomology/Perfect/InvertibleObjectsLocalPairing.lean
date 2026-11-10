module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsPairedSplitting
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsGlobalSplitting
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocalComplexMapOfARetraction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Representatives
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact
public import StacksFrontier.AlgebraicGeometry.Sites.OverMapComp
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedLocalPairing

/-!
# A derived isomorphism of strictly perfect complexes is locally a homotopy equivalence

Let `(C, O)` be a ringed site, `U` an object of `C`, and `A`, `B` strictly perfect complexes of
`O|_U`-modules which are isomorphic in `D(O|_U)`. Then along the arrows of a covering sieve of `U`
the restrictions of `A` and `B` are homotopy equivalent.

The isomorphism is a map of complexes along a covering (Stacks 08FR (1)), so is its inverse along
a refinement, and the two composites differ from the identities by maps killed in the derived
category, which are null-homotopic along a further refinement (Stacks 08FR (2)). This is the
step of the proof of `(1) ⟹ (2)` of Stacks 0FPY which turns the isomorphism
`O → M ⊗^L N` into maps of complexes `α`, `β` with `β ∘ α = 1` and `α ∘ β` homotopic to `1`.

## References

* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY)
* [Stacks Project, Tag 08FR](https://stacks.math.columbia.edu/tag/08FR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.DerivedMonoidal

universe u d

namespace AlgebraicGeometry.RingedSite.InvertibleDerived

open Stacks.Cohomology.InvertibleDerived (Q_map_comp_eq_id_of_factors homotopyEquivOfNullHomotopic)

variable (X : RingedSite.{u, u, u})
  [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restriction of complexes of `O|_U`-modules along an arrow `V ⟶ U` of the site. -/
abbrev restr {U V : X.C} (f : V ⟶ U) :
    CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ :=
  (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- Restricting twice is restricting along the composite. -/
def restrCompIso {U V W : X.C} (f : V ⟶ U) (g : W ⟶ V) :
    restr X f ⋙ restr X g ≅ restr X (g ≫ f) :=
  Functor.mapHomologicalComplexCompIso
    (Stacks.SheafOfModules.overMapCompIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f g)
    (ComplexShape.up ℤ)

/-- The sieve of arrows along which two complexes of `O|_U`-modules restrict to homotopy
equivalent complexes. -/
def homotopyEquivSieve (U : X.C)
    (A B : CochainComplex
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ) :
    Sieve U where
  arrows V f := Nonempty (HomotopyEquiv ((restr X f).obj A) ((restr X f).obj B))
  downward_closed := by
    rintro V W f ⟨h⟩ g
    exact ⟨(HomotopyEquiv.ofIso ((restrCompIso X f g).app A).symm).trans
      (((SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        g).mapHomotopyEquiv h).trans
        (HomotopyEquiv.ofIso ((restrCompIso X f g).app B)))⟩

/-- **A derived isomorphism of strictly perfect complexes is locally a homotopy equivalence.** -/
theorem homotopyEquivSieve_mem (U : X.C)
    {A B : CochainComplex
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) ℤ}
    (hA : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) A)
    (hB : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) B)
    [HasDerivedCategory.{d}
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]
    (φ : DerivedCategory.Q.obj A ≅ DerivedCategory.Q.obj B) :
    homotopyEquivSieve X U A B ∈ X.J U := by
  obtain ⟨S₁, hS₁, hrep⟩ := exists_coveringSieve_complexMap X U hA φ.hom
  refine X.J.transitive hS₁ _ fun V f hf => ?_
  let _ : HasDerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) :=
    HasDerivedCategory.standard _
  obtain ⟨hsheaf, hlocal, hadd, hlim, hcolim, a, ha⟩ := hrep f hf
  let H := SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f
  have hQa : IsIso (DerivedCategory.Q.map a) := by
    have : IsIso (H.mapDerivedCategoryFactors.hom.app A ≫ DerivedCategory.Q.map a) :=
      ha ▸ ((H.mapDerivedCategory.mapIso φ ≪≫ H.mapDerivedCategoryFactors.app B).isIso_hom)
    exact IsIso.of_isIso_comp_left (H.mapDerivedCategoryFactors.hom.app A) _
  have hB' := isStrictlyPerfect_overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f hB
  obtain ⟨S₂, hS₂, hrep₂⟩ := exists_coveringSieve_complexMap X V hB' (inv (DerivedCategory.Q.map a))
  refine X.J.transitive hS₂ _ fun W g hg => ?_
  let _ : HasDerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) :=
    HasDerivedCategory.standard _
  obtain ⟨hsheaf', hlocal', hadd', hlim', hcolim', b, hb⟩ := hrep₂ g hg
  obtain ⟨e₁, e₂⟩ := Q_map_comp_eq_id_of_factors
    (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) a b hb
  have h1 : DerivedCategory.Q.map ((restr X g).map a ≫ b - 𝟙 _) = 0 := by
    rw [Functor.map_sub, e₁, CategoryTheory.Functor.map_id, sub_self]
  have h2 : DerivedCategory.Q.map (b ≫ (restr X g).map a - 𝟙 _) = 0 := by
    rw [Functor.map_sub, e₂, CategoryTheory.Functor.map_id, sub_self]
  obtain ⟨S₃, hS₃, hn₃⟩ := exists_coveringSieve_homotopy_zero_of_derived_zero_overMap X W
    (isStrictlyPerfect_overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g
      (isStrictlyPerfect_overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f hA)) _ h1
  obtain ⟨S₄, hS₄, hn₄⟩ := exists_coveringSieve_homotopy_zero_of_derived_zero_overMap X W
    (isStrictlyPerfect_overMap (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g hB') _ h2
  refine X.J.superset_covering ?_ (X.J.intersection_covering hS₃ hS₄)
  rintro W' h ⟨h3, h4⟩
  obtain ⟨k₁⟩ := hn₃ h h3
  obtain ⟨k₂⟩ := hn₄ h h4
  let E := homotopyEquivOfNullHomotopic
    (SheafOfModules.overMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) h) _ _ k₁ k₂
  exact ⟨(HomotopyEquiv.ofIso (((restrCompIso X f (h ≫ g)).app A).symm ≪≫
      ((restrCompIso X g h).app ((restr X f).obj A)).symm)).trans (E.trans
    (HomotopyEquiv.ofIso (((restrCompIso X g h).app ((restr X f).obj B)) ≪≫
      ((restrCompIso X f (h ≫ g)).app B))))⟩

/-! ### The image of an idempotent on the structure sheaf is freely generated over the corners -/

section Gen

variable {Y : RingedSite.{u, u, u}} [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

open Stacks.Cohomology.InvertibleDerived (splitObj splitι splitπ splitι_splitπ splitπ_splitι
  splitι_comp)

/-- A section of the unit module, read as a section of `O`. -/
abbrev ofUnitSec {T : Y.C}
    (a : (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).val.obj (op T)) :
    (Y.O.obj.obj (op T) : Type u) := a

/-- A section of `O`, read as a section of the unit module. -/
abbrev unitSec {T : Y.C} (a : (Y.O.obj.obj (op T) : Type u)) :
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).val.obj (op T) := a

/-- **A module isomorphic to the image of an idempotent global section acting on `O` is freely
generated over the corners by one section.** -/
theorem exists_gen_of_iso_splitObj {G : Mod Y.O} (s : GlobalSection Y) (hs : s * s = s)
    (ψ : G ≅ splitObj (C := Mod Y.O) (smulHom s (SheafOfModules.unit _))) (T : Y.C) :
    ∃ t : G.val.obj (op T), ∀ ⦃W : Y.C⦄ (g : W ⟶ T),
      Function.Bijective fun c : {a : (Y.O.obj.obj (op W) : Type u) // s.val (op W) * a = a} =>
        ringSec c.1 • (G.val.map g.op t : G.val.obj (op W)) := by
  let p := smulHom s (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  have hp : p ≫ p = p := by
    change smulHom s _ ≫ smulHom s _ = smulHom s _
    rw [smulHom_comp, hs]
  let π : SheafOfModules.unit _ ⟶ splitObj p := splitπ hp
  let ι : splitObj p ⟶ SheafOfModules.unit _ := splitι p
  refine ⟨ψ.inv.val.app (op T) (π.val.app (op T) (unitSec 1)), ?_⟩
  intro W g
  have n1 : (G.val.map g.op (ψ.inv.val.app (op T) (π.val.app (op T) (unitSec 1))) :
      G.val.obj (op W)) = ψ.inv.val.app (op W) (π.val.app (op W) (unitSec 1)) := by
    rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
    congr 2
    exact map_one (Y.O.obj.map g.op).hom
  have key : ∀ c : (Y.O.obj.obj (op W) : Type u),
      ringSec c • (G.val.map g.op (ψ.inv.val.app (op T) (π.val.app (op T) (unitSec 1))) :
        G.val.obj (op W)) = ψ.inv.val.app (op W) (π.val.app (op W) (unitSec c)) := by
    intro c
    rw [n1]
    refine ((ψ.inv.val.app (op W)).hom.map_smul _ _).symm.trans ?_
    refine congrArg (ψ.inv.val.app (op W)) (((π.val.app (op W)).hom.map_smul _ _).symm.trans ?_)
    congr 1
    exact mul_one c
  have hιπ : ∀ c : (Y.O.obj.obj (op W) : Type u),
      ι.val.app (op W) (π.val.app (op W) (unitSec c)) = unitSec (s.val (op W) * c) := fun c =>
    congrArg (fun φ : SheafOfModules.unit _ ⟶ SheafOfModules.unit _ => φ.val.app (op W) (unitSec c))
      (splitπ_splitι hp)
  have hπι : ∀ x, π.val.app (op W) (ι.val.app (op W) x) = x := fun x =>
    congrArg (fun φ : splitObj p ⟶ splitObj p => φ.val.app (op W) x) (splitι_splitπ hp)
  have hιs : ∀ x, unitSec (s.val (op W) * ofUnitSec (ι.val.app (op W) x)) =
      ι.val.app (op W) x := fun x =>
    congrArg (fun φ : splitObj p ⟶ SheafOfModules.unit _ => φ.val.app (op W) x) (splitι_comp hp)
  have hinv : ∀ a b, ψ.inv.val.app (op W) a = ψ.inv.val.app (op W) b → a = b := by
    intro a b h
    have := congrArg (ψ.hom.val.app (op W)) h
    change (ψ.inv ≫ ψ.hom).val.app (op W) a = (ψ.inv ≫ ψ.hom).val.app (op W) b at this
    rwa [Iso.inv_hom_id] at this
  refine ⟨fun a b h => Subtype.ext ?_, fun x => ?_⟩
  · have := congrArg (ι.val.app (op W)) (hinv _ _ ((key a.1).symm.trans (h.trans (key b.1))))
    rw [hιπ, hιπ] at this
    exact a.2.symm.trans ((congrArg ofUnitSec this).trans b.2)
  · let x' := ψ.hom.val.app (op W) x
    refine ⟨⟨ofUnitSec (ι.val.app (op W) x'), congrArg ofUnitSec (hιs x')⟩, ?_⟩
    refine (key _).trans ?_
    change ψ.inv.val.app (op W) (π.val.app (op W) (ι.val.app (op W) x')) = x
    rw [hπι]
    change (ψ.hom ≫ ψ.inv).val.app (op W) x = x
    rw [Iso.hom_inv_id]
    rfl

end Gen

end AlgebraicGeometry.RingedSite.InvertibleDerived

end
