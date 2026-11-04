module

public import Mathlib.NumberTheory.Zsqrtd.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRank
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Defs
public import StacksFrontier.RingTheory.Ideal.Invertible
import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.LocalUnitConditions
import StacksCore.Tactic.StacksAttribute

/-!
# Invertible modules and locally free modules of rank one on a ringed site

Let `(Sh(C), O)` be the ringed topos of a ringed site. A sheaf of `O`-modules which is locally
free of rank one is invertible, with no hypothesis on the site. On a locally ringed site the
converse holds as well, and without local ringedness it fails: the one-object site carrying a
Dedekind domain with nontrivial class group has an invertible module of no rank.

## Main results

* `AlgebraicGeometry.RingedSite.isInvertible_of_isFiniteLocallyFreeOfRank_one`: a module of
  rank one is invertible.
* `AlgebraicGeometry.RingedSite.isInvertible_iff_isFiniteLocallyFreeOfRank_one`: on a locally
  ringed site, invertibility is equivalent to being locally free of rank one.
* `AlgebraicGeometry.RingedSite.exists_isInvertible_not_isFiniteLocallyFreeOfRank_one`: an
  invertible module on a ringed site which is not locally free of rank one.

## Implementation notes

Invertibility is `Stacks.SheafOfModules.IsInvertible`, the condition of Tag 01CS that tensoring
is an equivalence; rank one is
`AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank _ _ 1`, the covering-family condition of
Tag 0409 imposed over every object of the site; and local ringedness is
`AlgebraicGeometry.RingedSite.IsLocallyRinged`, the pair of conditions of Tag 04EU.

The unconditional direction constructs the evaluation pairing against the internal Hom
`Hom_O(L, O)` of Tag 03EM and checks that it is bijective over every member of a trivializing
covering, which makes it invertible after sheafification. The required sheafification instances
are produced from the essentially small model of the site, so the statement needs no hypothesis
beyond the site itself.

The converse does not go through the projector matrices of the source proof. From invertibility
one gets `N` with `L ⊗_O N ≅ O` (Tag 0B8K), lifts `1` locally to a finite sum `∑ s_i ⊗ t_i`, and
the local-unit criterion of Tag 04ES — which is where local ringedness enters — produces a
covering on which one pairing `⟨s_i, t_i⟩` is a unit. Rescaling `s_i` by that unit gives a
section of `L` by which multiplication is bijective over the whole slice site, hence a
trivialization.

Two spellings of the structure sheaf of rings. `Stacks.SheafOfModules.Tensor.ringSheaf X.O` has
as underlying presheaf `X.O.obj` composed with `forget₂ CommRingCat RingCat`, and
`Oforget X.O.obj` is the reducible abbreviation for that same composition. The sections of a
sheaf of modules are modules over the first spelling, while the internal Hom of Tag 03EM and
the slice-site scalars `ORestr` of Tag 03EH are stated at the second, and instance search does
not cross from one to the other: it unfolds only reducible
definitions, and neither `Tensor.ringSheaf` nor `ORestr` is one. Both are made to unfold here
instead, which is what lets every statement below name the sheaf of modules by its canonical
`L.val` and its scalars by `Oforget X.O.obj`, with no local re-spelling of either and no
`map_smul` of its own for a section of the internal Hom.

Local bijectivity of a composite with an isomorphism is a separate matter, and is stated here as
the closed lemma `isLocallyBijective_comp_of_isIso`. Mathlib derives `IsLocallyInjective` and
`IsLocallySurjective` from `IsIso`, but that derivation does not fire at the concrete second
factor of `exists_cover_generatorSections` — an image of a morphism of sheaves of modules under
two functors — even with `IsIso` for it in the local context as an instance; abstracting the two
morphisms to variables is what makes it fire.

Universes. The objects of the site, its morphisms and the sections of the structure sheaf are
independent for the unconditional direction, where the sections only have to be large enough to
hold the internal Hom. The equivalence puts the morphisms and the sections in one universe,
because the local-unit criterion of Tag 04ES is stated for a structure sheaf whose sections lie
in the morphism universe of the site.

## References

* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 04ES](https://stacks.math.columbia.edu/tag/04ES)
* [Stacks Project, Tag 04EU](https://stacks.math.columbia.edu/tag/04EU)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v w

namespace AlgebraicGeometry.RingedSite

attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local implicit_reducible] ORestr

private inductive OneSiteObject : Type u
  | star

private abbrev oneSiteCategory : Category.{v} OneSiteObject where
  Hom _ _ := PUnit.{v + 1}
  id _ := PUnit.unit
  comp _ _ := PUnit.unit
  id_comp := by intros; exact Subsingleton.elim _ _
  comp_id := by intros; exact Subsingleton.elim _ _
  assoc := by intros; exact Subsingleton.elim _ _

private noncomputable def pointRingedSite (A : CommRingCat.{w}) :
    AlgebraicGeometry.RingedSite.{u, v, w} := by
  letI : Category.{v} OneSiteObject := oneSiteCategory
  exact {
    C := OneSiteObject
    category := inferInstance
    J := ⊥
    O := ⟨(Functor.const (OneSiteObjectᵒᵖ)).obj A, Presheaf.isSheaf_bot _⟩ }

private noncomputable def constantModulePresheaf
    (A : CommRingCat.{w}) (M : ModuleCat.{w} A) :
    PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedSite A).O).obj where
  obj _ := M
  map _ := 𝟙 _
  map_id _ := by rfl
  map_comp _ _ := by rfl

private noncomputable def constantModuleSheaf
    (A : CommRingCat.{w}) (M : ModuleCat.{w} A) :
  SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedSite A).O) :=
  ⟨constantModulePresheaf A M, Presheaf.isSheaf_bot _⟩

private noncomputable def pointTensorFunctor
    (A : CommRingCat.{w})
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedSite A).O)) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedSite A).O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedSite A).O) := by
  exact {
    obj := fun M => ⟨(tensorLeft L.val).obj M.val, Presheaf.isSheaf_bot _⟩
    map := fun f => ⟨(tensorLeft L.val).map f.val⟩
    map_id := by intro M; ext U x; simp
    map_comp := by intro M N P f g; ext U x; simp }

private noncomputable def pointTensorFunctorUniversal
    (A : CommRingCat.{w})
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedSite A).O)) :
    Stacks.SheafOfModules.TensorLeftUniversal (pointRingedSite A).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedSite A).O).property L
      (pointTensorFunctor A L) := by
  let F := pointTensorFunctor A L
  refine ⟨?_, ?_⟩
  · refine { app := fun M => 𝟙 ((tensorLeft L.val).obj M.val), naturality := ?_ }
    intro M N f
    change (tensorLeft L.val).map f.val ≫ 𝟙 _ = 𝟙 _ ≫ (tensorLeft L.val).map f.val
    simp
  · intro M N
    change Function.Bijective (fun f : F.obj M ⟶ N =>
      (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedSite A).O)).map f)
    constructor
    · intro f g h
      exact (SheafOfModules.fullyFaithfulForget
        (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedSite A).O)).map_injective h
    · intro f
      obtain ⟨g, hg⟩ :=
        (SheafOfModules.fullyFaithfulForget
          (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedSite A).O)).map_surjective f
      exact ⟨g, hg⟩

private noncomputable def pointTensorCancelIso
    (A : CommRingCat.{w}) (M N : ModuleCat.{w} A)
    (e : TensorProduct A N M ≃ₗ[A] A) :
    pointTensorFunctor A (constantModuleSheaf A M) ⋙
      pointTensorFunctor A (constantModuleSheaf A N) ≅ 𝟭 _ := by
  let c (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedSite A).O)) :
      (pointTensorFunctor A (constantModuleSheaf A N)).obj
        ((pointTensorFunctor A (constantModuleSheaf A M)).obj F) ≅ F := by
    apply (SheafOfModules.fullyFaithfulForget
      (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedSite A).O)).preimageIso
    refine PresheafOfModules.isoMk (fun U => ?_) ?_
    · let P : ModuleCat.{w} A := F.val.obj U
      exact (Module.Invertible.leftCancelEquiv P e).toModuleIso
    · intro X Y f
      rcases X with ⟨⟨⟩⟩
      rcases Y with ⟨⟨⟩⟩
      have hf : f = 𝟙 _ := by
        apply Quiver.Hom.unop_inj
        exact @Subsingleton.elim PUnit _ _ _
      subst f
      ext x
      simp only [PresheafOfModules.map_id]
      rfl
  refine NatIso.ofComponents c ?_
  intro F G f
  apply (SheafOfModules.fullyFaithfulForget
    (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedSite A).O)).map_injective
  ext U x
  let P : ModuleCat.{w} A := F.val.obj U
  let Q : ModuleCat.{w} A := G.val.obj U
  let f' : P ⟶ Q := f.val.app U
  have h := Module.Invertible.leftCancelEquiv_comp_lTensor_comp_symm e f'.hom
  rw [← LinearMap.comp_assoc, LinearEquiv.comp_toLinearMap_symm_eq] at h
  exact LinearMap.congr_fun h x

private theorem isInvertible_constantModuleSheaf
    (A : CommRingCat.{w}) (M : ModuleCat.{w} A) [Module.Invertible A M] :
    Stacks.SheafOfModules.IsInvertible (pointRingedSite A).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedSite A).O).property
      (constantModuleSheaf A M) := by
  let N := ModuleCat.of A (Module.Dual A M)
  let e := Module.Invertible.linearEquiv A M
  let F := pointTensorFunctor A (constantModuleSheaf A M)
  let G := pointTensorFunctor A (constantModuleSheaf A N)
  let E := CategoryTheory.Equivalence.mk F G (pointTensorCancelIso A M N e).symm
    (pointTensorCancelIso A N M ((TensorProduct.comm A M N).trans e))
  exact ⟨F, E.isEquivalence_functor, ⟨pointTensorFunctorUniversal A _⟩⟩

private noncomputable def unitCofanFinOneColimit
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w}} :
    IsColimit (Cofan.mk (SheafOfModules.unit R)
      (fun _ : Fin 1 => 𝟙 (SheafOfModules.unit R))) := by
  refine Cofan.IsColimit.mk _ (fun s => s.inj 0) ?_ ?_
  · intro s j
    fin_cases j
    simp
  · intro s m hm
    simpa using hm 0

/-- A presentation as a coproduct of one copy of the unit module is an
isomorphism with the unit. -/
private noncomputable def locallyFreeRankOneIso
    (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (V : X.C) (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (ι : ∀ _ : Fin 1,
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) ⟶ F.over V)
    (hι : Nonempty (IsColimit (Cofan.mk (F.over V) ι))) :
    F.over V ≅ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) := by
  let hc := unitCofanFinOneColimit (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
  exact (hc.coconePointUniqueUpToIso (Classical.choice hι)).symm

private theorem linearEquiv_of_constantModuleSheaf_rank_one
    (A : CommRingCat.{w}) (M : ModuleCat.{w} A)
    (h : AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank
      (pointRingedSite A : AlgebraicGeometry.RingedSite.{u, v, w})
      (constantModuleSheaf A M) 1) :
    Nonempty (M ≃ₗ[A] A) := by
  let X : AlgebraicGeometry.RingedSite.{u, v, w} := pointRingedSite A
  let U : X.C := OneSiteObject.star
  obtain ⟨I, V, f, hf, hi⟩ := h U
  have htop : Sieve.ofArrows (C := X.C) V f = ⊤ := hf
  have hid : (Sieve.ofArrows (C := X.C) V f).arrows (𝟙 U) := by
    rw [htop]
    trivial
  obtain ⟨i, g, hg⟩ := Sieve.ofArrows.exists hid
  obtain ⟨ι, hι⟩ := hi i
  let e := locallyFreeRankOneIso (pointRingedSite A) (V i)
    (constantModuleSheaf A M) ι hι
  exact ⟨((SheafOfModules.evaluation
    ((Stacks.SheafOfModules.Tensor.ringSheaf (pointRingedSite A).O).over (V i))
    (Opposite.op (Over.mk (𝟙 (V i))))).mapIso e).toLinearEquiv⟩

private theorem exists_isInvertible_not_rank_one_of_module
    (A : CommRingCat.{w}) (M : ModuleCat.{w} A) [Module.Invertible A M]
    (hM : ¬ Nonempty (M ≃ₗ[A] A)) :
    ∃ (X : AlgebraicGeometry.RingedSite.{u, v, w})
      (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
      Stacks.SheafOfModules.IsInvertible X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L ∧
        ¬ AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank X L 1 := by
  refine ⟨pointRingedSite A, constantModuleSheaf A M,
    isInvertible_constantModuleSheaf A M, fun h => ?_⟩
  exact hM (linearEquiv_of_constantModuleSheaf_rank_one A M h)

private theorem exists_cover_localUnit
    (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hL : AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank X L 1)
    (U : X.C) :
    ∃ (I : Type (max u v)) (V : I → X.C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ X.J U ∧
        ∀ i, Nonempty (L.over (V i) ≅
          SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (V i))) := by
  obtain ⟨I, V, f, hcov, hfree⟩ := hL U
  refine ⟨I, V, f, hcov, fun i => ⟨locallyFreeRankOneIso X (V i) L (hfree i).choose
    (hfree i).choose_spec⟩⟩

private theorem isFiniteLocallyFreeOfRank_one_of_exists_cover_localUnit
    (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (h : ∀ U : X.C,
      ∃ (I : Type (max u v)) (V : I → X.C) (f : ∀ i, V i ⟶ U),
        Sieve.ofArrows V f ∈ X.J U ∧
          ∀ i, Nonempty (L.over (V i) ≅
            SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (V i)))) :
    AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank X L 1 := by
  intro U
  obtain ⟨I, V, f, hcov, hiso⟩ := h U
  refine ⟨I, V, f, hcov, fun i => ?_⟩
  let e := Classical.choice (hiso i)
  let ι : ∀ _ : Fin 1,
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (V i)) ⟶
        L.over (V i) :=
    fun _ => e.inv
  refine ⟨ι, ⟨IsColimit.ofIsoColimit unitCofanFinOneColimit (Cocone.ext e.symm ?_)⟩⟩
  rintro ⟨j⟩
  fin_cases j
  simp [ι, e]


private noncomputable def dualEvaluation
    (X : AlgebraicGeometry.RingedSite.{u, v, max u v w})
    (L : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    L.val ⊗ internalHom X.O.obj L.val
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val ⟶
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val := by
  let D := internalHom X.O.obj L.val
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val
  refine PresheafOfModules.Hom.mk (fun U =>
    ModuleCat.MonoidalCategory.tensorLift
      (fun (x : L.val.obj U) a =>
        (a.app (Opposite.op (Over.mk (𝟙 U.unop)))).hom x)
      (by intros; exact map_add _ _ _)
      (by intro c x a; exact map_smul _ _ _)
      (by intros; rfl)
      (by
        intro r x a
        change (show (Oforget X.O.obj).obj U from (X.O.obj.map (𝟙 U.unop).op).hom r) *
          (show (Oforget X.O.obj).obj U from
            (a.app (Opposite.op (Over.mk (𝟙 U.unop)))).hom x) =
          (show (Oforget X.O.obj).obj U from r) *
            (show (Oforget X.O.obj).obj U from
              (a.app (Opposite.op (Over.mk (𝟙 U.unop)))).hom x)
        simp)) ?_
  intro U V f
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x a
  change (a.app (Opposite.op (Over.mk (𝟙 V.unop ≫ f.unop)))).hom
    (L.val.map f x) =
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val.map f
      ((a.app (Opposite.op (Over.mk (𝟙 U.unop)))).hom x)
  rw [Category.id_comp]
  exact PresheafOfModules.naturality_apply a
    (Over.homMk f.unop (by simp) : Over.mk f.unop ⟶ Over.mk (𝟙 U.unop)).op x

private theorem unitHom_ext_of_isTerminal
    {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}
    {M : PresheafOfModules.{w} R} {U : C} (hU : IsTerminal U)
    (f g : PresheafOfModules.unit R ⟶ M)
    (h : f.app (Opposite.op U) (1 : R.obj (Opposite.op U)) =
      g.app (Opposite.op U) (1 : R.obj (Opposite.op U))) : f = g := by
  apply M.unitHomEquiv.injective
  apply Subtype.ext
  funext V
  have hf := (M.unitHomEquiv f).property (hU.from V.unop).op
  have hg := (M.unitHomEquiv g).property (hU.from V.unop).op
  exact hf.symm.trans ((congrArg _ h).trans hg)

private noncomputable def localDualEquiv
    (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (e : L.over U ≅ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :
    (internalHom X.O.obj L.val
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val).obj (Opposite.op U)
      ≃ₗ[(Oforget X.O.obj).obj (Opposite.op U)] (Oforget X.O.obj).obj (Opposite.op U) := by
  let T : (Over U)ᵒᵖ := Opposite.op (Over.mk (𝟙 U))
  let φ : (internalHom X.O.obj L.val
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val).obj (Opposite.op U)
      →ₗ[(Oforget X.O.obj).obj (Opposite.op U)] (Oforget X.O.obj).obj (Opposite.op U) :=
    { toFun := fun a => a.app T (e.inv.val.app T (1 : (Oforget X.O.obj).obj (Opposite.op U)))
      map_add' := by intros; rfl
      map_smul' := by
        intro r a
        change (show (Oforget X.O.obj).obj (Opposite.op U) from
          (X.O.obj.map (𝟙 U).op).hom r) * _ = _
        simp
        rfl }
  apply LinearEquiv.ofBijective φ
  constructor
  · intro a b hab
    have : IsIso e.inv.val := (SheafOfModules.forget _).map_isIso e.inv
    apply (cancel_epi e.inv.val).mp
    exact unitHom_ext_of_isTerminal (Over.mkIdTerminal (X := U)) _ _ hab
  · intro r
    refine ⟨smulHom X.O.obj L.val
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val U r e.hom.val, ?_⟩
    have he : e.hom.val.app T (e.inv.val.app T
          (1 : (Oforget X.O.obj).obj (Opposite.op U))) =
        (1 : (Oforget X.O.obj).obj (Opposite.op U)) :=
      ConcreteCategory.congr_hom
        (congrArg
          (fun f : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶
            SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) =>
              f.val.app T)
          e.inv_hom_id)
        (1 : (Oforget X.O.obj).obj (Opposite.op U))
    change (show (Oforget X.O.obj).obj (Opposite.op U) from
        (X.O.obj.map (𝟙 U).op).hom r) *
      (show (Oforget X.O.obj).obj (Opposite.op U) from e.hom.val.app T (e.inv.val.app T
        (1 : (Oforget X.O.obj).obj (Opposite.op U)))) = r
    rw [he]
    simp

private theorem dualEvaluation_bijective
    (X : AlgebraicGeometry.RingedSite.{u, v, max u v w})
    (L : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C)
    (e : L.over U ≅ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :
    Function.Bijective ((dualEvaluation X L).app (Opposite.op U)) := by
  let T : (Over U)ᵒᵖ := Opposite.op (Over.mk (𝟙 U))
  let eL : (L.val.obj (Opposite.op U)) ≃ₗ[(Oforget X.O.obj).obj (Opposite.op U)]
      (Oforget X.O.obj).obj (Opposite.op U) :=
    ((SheafOfModules.evaluation ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) T).mapIso
      e).toLinearEquiv
  let eD := localDualEquiv X L U e
  let E := (TensorProduct.congr eL eD).trans (TensorProduct.lid _ _)
  have h : ((dualEvaluation X L).app (Opposite.op U)).hom = E.toLinearMap := by
    apply TensorProduct.ext
    ext x a
    change a.app T x =
      (show (Oforget X.O.obj).obj (Opposite.op U) from eL x) * eD a
    have hx : x = eL x • eL.symm 1 := by
      rw [← map_smul]
      simp
    exact (congrArg (a.app T) hx).trans (map_smul _ _ _)
  change Function.Bijective ((dualEvaluation X L).app (Opposite.op U)).hom
  rw [h]
  exact E.bijective

noncomputable local instance (X : AlgebraicGeometry.RingedSite.{u, v, max u v w}) :
    HasSheafify X.J AddCommGrpCat.{max u v w} := by
  let : EssentiallySmall.{max u v w} X.C := essentiallySmallSelf X.C
  let : SmallCategory (SmallModel.{max u v w} X.C) := smallCategorySmallModel X.C
  let K : GrothendieckTopology (SmallModel.{max u v w} X.C) :=
    (equivSmallModel.{max u v w} X.C).inverse.inducedTopology X.J
  have : HasSheafify K AddCommGrpCat.{max u v w} := inferInstance
  exact hasSheafifyEssentiallySmallSite.{v, max u v w, u, (max u v w)+1, max u v w}
    X.J AddCommGrpCat.{max u v w}

local instance (X : AlgebraicGeometry.RingedSite.{u, v, max u v w}) :
    X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w} := by
  let : EssentiallySmall.{max u v w} X.C := essentiallySmallSelf X.C
  let : SmallCategory (SmallModel.{max u v w} X.C) := smallCategorySmallModel X.C
  let K : GrothendieckTopology (SmallModel.{max u v w} X.C) :=
    (equivSmallModel.{max u v w} X.C).inverse.inducedTopology X.J
  have : K.WEqualsLocallyBijective AddCommGrpCat.{max u v w} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v,
    max u v w, u, (max u v w)+1, max u v w, max u v w, max u v w} X.J

private theorem isIso_sheafify_of_cover_bijective
    (X : AlgebraicGeometry.RingedSite.{u, v, max u v w})
    {M N : PresheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj}
    (φ : M ⟶ N)
    (h : ∀ U : X.C, ∃ (I : Type (max u v)) (V : I → X.C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ X.J U ∧
        ∀ i, Function.Bijective (φ.app (Opposite.op (V i)))) :
    IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).map φ) := by
  let ψ := (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).map φ
  have hw : X.J.W ψ := by
    apply (X.J.W_iff_isLocallyBijective ψ).mpr
    constructor
    · constructor
      intro U x y hxy
      obtain ⟨I, V, f, hf, hi⟩ := h U.unop
      apply X.J.superset_covering _ hf
      apply (Sieve.generate_le_iff _ _).mpr
      rintro W g ⟨i⟩
      apply (hi i).injective
      change (φ.app (Opposite.op (V i))).hom (M.map (f i).op x) =
        (φ.app (Opposite.op (V i))).hom (M.map (f i).op y)
      exact (PresheafOfModules.naturality_apply φ (f i).op x).trans
        ((congrArg (N.map (f i).op) hxy).trans
          (PresheafOfModules.naturality_apply φ (f i).op y).symm)
    · constructor
      intro U x
      obtain ⟨I, V, f, hf, hi⟩ := h U
      apply X.J.superset_covering _ hf
      apply (Sieve.generate_le_iff _ _).mpr
      rintro W g ⟨i⟩
      exact (hi i).surjective _
  change (MorphismProperty.isomorphisms _).inverseImage
    (PresheafOfModules.sheafification.{max u v w}
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)) φ
  rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms.{max u v w,
    max u v w, v, u} (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)]
  exact hw

/-- **Stacks Project, Tag 0B8Q**, the unconditional clause. On the ringed topos of a ringed
site, a sheaf of modules which is locally free of rank one is invertible. -/
@[stacks 0B8Q "locally free of rank one implies invertible"]
theorem isInvertible_of_isFiniteLocallyFreeOfRank_one
    (X : AlgebraicGeometry.RingedSite.{u, v, max u v w})
    (L : SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hL : AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank X L 1) :
    Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L := by
  let D : SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
    ⟨internalHom X.O.obj L.val
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val,
      internalHom_isSheaf _ _ _
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).isSheaf⟩
  let φ := dualEvaluation X L
  have hφ : IsIso ((Stacks.SheafOfModules.TensorSheafification.sheafify X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).map φ) := by
    apply isIso_sheafify_of_cover_bijective X
    intro U
    obtain ⟨I, V, f, hf, hi⟩ := exists_cover_localUnit X L hL U
    exact ⟨I, V, f, hf, fun i => dualEvaluation_bijective X L (V i)
      (Classical.choice (hi i))⟩
  apply (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (O := X.O.obj) (hO := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) L).mpr
  exact ⟨D, ⟨@asIso _ _ _ _ _ hφ ≪≫
    (Stacks.SheafOfModules.forgetSheafifyIso X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property).app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))⟩⟩

private abbrev GeneratorSections (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (U : X.C) :=
  {s : L.val.obj (Opposite.op U) //
    ∀ (V : X.C) (f : V ⟶ U),
      Function.Bijective (fun r : (Oforget X.O.obj).obj (Opposite.op V) =>
        r • L.val.restrictₛₗ f.op s)}

/-- A section that generates an invertible module over every arrow to `U`
trivializes that module on the slice site over `U`. -/
private noncomputable def generatorSectionsIso
    (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (U : X.C) (s : GeneratorSections X L U) :
    L.over U ≅ SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) := by
  let sec : (L.over U).val.sections :=
    PresheafOfModules.sectionsMk (fun W => L.val.map W.unop.hom.op s.val) (by
      intro W W' f
      change L.val.map f.unop.left.op (L.val.map W.unop.hom.op s.val) = _
      rw [← L.val.map_comp_apply]
      change L.val.map (f.unop.left ≫ W.unop.hom).op s.val = _
      rw [f.unop.w])
  let φ : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U) ⟶ L.over U :=
    ⟨(L.over U).val.unitHomEquiv.symm sec⟩
  have hφ (W : (Over U)ᵒᵖ) : IsIso (φ.val.app W) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (s.property W.unop.left W.unop.hom)
  have ψ : (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)).val ≅
      (L.over U).val :=
    PresheafOfModules.isoMk (fun W => @asIso _ _ _ _ (φ.val.app W) (hφ W))
      (by intro W W' f; exact φ.val.naturality f)
  exact ((SheafOfModules.fullyFaithfulForget
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)).preimageIso
    (X := SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))
    (Y := L.over U) ψ).symm

/-- A pairing taking the value one makes tensoring with its second argument
injective. This is applied only after equality has been obtained locally. -/
private theorem tensor_right_injective_of_pairing_one
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (B : TensorProduct R M N →ₗ[R] R) (s : M) (t : N) (h : B (s ⊗ₜ t) = 1) :
    Function.Injective (fun x : M => x ⊗ₜ[R] t) := by
  let c := (TensorProduct.rid R M).toLinearMap.comp
    (TensorProduct.map LinearMap.id (B.comp (TensorProduct.mk R M N s)))
  intro x y hxy
  have hc := congrArg c hxy
  simpa [c, h] using hc

/-- A pairing is linear in its first argument. -/
private theorem pairing_smul_tmul {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (B : TensorProduct R M N →ₗ[R] R) (r : R) (s : M) (t : N) :
    B ((r • s) ⊗ₜ t) = r * B (s ⊗ₜ t) := by
  rw [← TensorProduct.smul_tmul', map_smul, smul_eq_mul]

private noncomputable abbrev pairingLinearMap
    (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (L N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (B : L.val ⊗ N.val ⟶ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val)
    (U : X.C) :
    TensorProduct ((Oforget X.O.obj).obj (Opposite.op U))
      (L.val.obj (Opposite.op U)) (N.val.obj (Opposite.op U))
      →ₗ[(Oforget X.O.obj).obj (Opposite.op U)] (Oforget X.O.obj).obj (Opposite.op U) :=
  (B.app (Opposite.op U)).hom

private theorem pairing_restrict
    (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (L N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (B : L.val ⊗ N.val ⟶ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val)
    {U V : X.C} (f : V ⟶ U)
    (s : L.val.obj (Opposite.op U)) (t : N.val.obj (Opposite.op U)) :
    (pairingLinearMap X L N B V)
        (L.val.restrictₛₗ f.op s ⊗ₜ N.val.restrictₛₗ f.op t) =
      (X.O.obj.map f.op).hom ((pairingLinearMap X L N B U) (s ⊗ₜ t)) := by
  exact PresheafOfModules.naturality_apply B f.op (s ⊗ₜ t)

/-- Local injectivity of the tensor pairing and a pair with value one give a
basis consisting of its first argument. Equality descends because `L` is a sheaf. -/
private theorem smul_bijective_of_pairing_one
    (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (L N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (B : L.val ⊗ N.val ⟶ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val)
    [Presheaf.IsLocallyInjective X.J
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).map B)]
    (U : X.C) (s : L.val.obj (Opposite.op U))
    (t : N.val.obj (Opposite.op U))
    (hst : (pairingLinearMap X L N B U) (s ⊗ₜ t) = 1) :
    Function.Bijective (fun r : (Oforget X.O.obj).obj (Opposite.op U) => r • s) := by
  let b := (pairingLinearMap X L N B U)
  have hb (r : (Oforget X.O.obj).obj (Opposite.op U)) : b ((r • s) ⊗ₜ t) = r := by
    rw [pairing_smul_tmul, hst, mul_one]
  constructor
  · intro r q hrq
    rw [← hb r, ← hb q]
    exact congrArg (fun x => b (x ⊗ₜ t)) hrq
  · intro x
    refine ⟨b (x ⊗ₜ t), ?_⟩
    let y := b (x ⊗ₜ t) • s
    let ψ := (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).map B
    have he : ψ.app (Opposite.op U) (y ⊗ₜ t) = ψ.app (Opposite.op U) (x ⊗ₜ t) :=
      hb (b (x ⊗ₜ t))
    let S := Presheaf.equalizerSieve (F := (L.val ⊗ N.val).presheaf) (y ⊗ₜ t) (x ⊗ₜ t)
    have hS : S ∈ X.J U := Presheaf.equalizerSieve_mem X.J ψ _ _ he
    have hL := Presheaf.isSheaf_comp_of_isSheaf X.J L.val.presheaf
      (forget AddCommGrpCat) L.isSheaf
    apply (hL.isSheafFor S hS).isSeparatedFor.ext
    intro V f hf
    have hst' : (pairingLinearMap X L N B V)
        (L.val.restrictₛₗ f.op s ⊗ₜ N.val.restrictₛₗ f.op t) = 1 := by
      rw [pairing_restrict, hst, map_one]
    exact tensor_right_injective_of_pairing_one (pairingLinearMap X L N B V)
      (L.val.restrictₛₗ f.op s) (N.val.restrictₛₗ f.op t) hst' hf

private theorem generatorSections_of_pairing_unit
    (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (L N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (B : L.val ⊗ N.val ⟶ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val)
    [Presheaf.IsLocallyInjective X.J
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).map B)]
    (U : X.C) (s : L.val.obj (Opposite.op U))
    (t : N.val.obj (Opposite.op U))
    (hst : IsUnit ((pairingLinearMap X L N B U) (s ⊗ₜ t))) :
    Nonempty (GeneratorSections X L U) := by
  obtain ⟨a, ha⟩ := hst
  let s' := (↑a⁻¹ : (Oforget X.O.obj).obj (Opposite.op U)) • s
  have hs' : (pairingLinearMap X L N B U) (s' ⊗ₜ t) = 1 := by
    change (pairingLinearMap X L N B U)
      (((↑a⁻¹ : (Oforget X.O.obj).obj (Opposite.op U)) • s) ⊗ₜ t) = 1
    rw [pairing_smul_tmul, ← ha, Units.inv_mul]
  refine ⟨⟨s', fun V f => ?_⟩⟩
  apply smul_bijective_of_pairing_one X L N B V _ (N.val.restrictₛₗ f.op t)
  rw [pairing_restrict, hs', map_one]

/-- A composite of presheaf morphisms whose first factor is locally bijective and whose second
factor is an isomorphism is locally bijective. The two morphisms are variables here, which is
what makes Mathlib's derivation of local injectivity and local surjectivity from `IsIso` fire:
at the concrete second factor of `exists_cover_generatorSections`, an image of a morphism of
sheaves of modules under two functors, it does not fire, even with `IsIso` for that morphism in
the local context as an instance. -/
private theorem isLocallyBijective_comp_of_isIso {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {F₁ F₂ F₃ : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    (φ : F₁ ⟶ F₂) (ψ : F₂ ⟶ F₃)
    (hinj : Presheaf.IsLocallyInjective J φ) (hsur : Presheaf.IsLocallySurjective J φ)
    (hiso : IsIso ψ) :
    Presheaf.IsLocallyInjective J (φ ≫ ψ) ∧ Presheaf.IsLocallySurjective J (φ ≫ ψ) :=
  ⟨Presheaf.isLocallyInjective_comp J φ ψ, Presheaf.isLocallySurjective_comp J φ ψ⟩

/-- Lift one locally to the tensor product, write the lift as a finite sum,
and use the local-ring criterion to find a term whose pairing is a unit. -/
@[ega "0 5.4.3" "more general"]
private theorem exists_cover_generatorSections
    (X : AlgebraicGeometry.RingedSite.{u, max u v, max u v})
    (L : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X)
    (hL : Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L)
    (U : X.C) :
    ∃ S : Sieve U, S ∈ X.J U ∧ ∀ ⦃V : X.C⦄ (f : V ⟶ U),
      S f → Nonempty (GeneratorSections X L V) := by
  obtain ⟨N, ⟨e⟩⟩ :=
    (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
      (O := X.O.obj) (hO := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property) L).mp hL
  let P := L.val ⊗ N.val
  let η := Stacks.SheafOfModules.TensorSheafification.toSheafify X.O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property P
  let B : P ⟶ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val :=
    η ≫ e.hom.val
  let ψ := (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).map B
  have hηinj : Presheaf.IsLocallyInjective X.J
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).map η) := by
    change Presheaf.IsLocallyInjective X.J (CategoryTheory.toSheafify X.J P.presheaf)
    infer_instance
  have hηsur : Presheaf.IsLocallySurjective X.J
      ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).map η) := by
    change Presheaf.IsLocallySurjective X.J (CategoryTheory.toSheafify X.J P.presheaf)
    infer_instance
  have hev : IsIso e.hom.val :=
    @CategoryTheory.Functor.map_isIso _ _ _ _ _ _
      (SheafOfModules.forget _) e.hom (CategoryTheory.Iso.isIso_hom e)
  have hiso : IsIso ((PresheafOfModules.toPresheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).map e.hom.val) :=
    @CategoryTheory.Functor.map_isIso _ _ _ _ _ _
      (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) e.hom.val hev
  have hcomp := isLocallyBijective_comp_of_isIso X.J
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).map η)
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).map
      e.hom.val) hηinj hηsur hiso
  have hψ : ψ = (PresheafOfModules.toPresheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).map η ≫
      (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).map
        e.hom.val :=
    (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).map_comp
      η e.hom.val
  have hψinj : Presheaf.IsLocallyInjective X.J ψ := by rw [hψ]; exact hcomp.1
  have hψsur : Presheaf.IsLocallySurjective X.J ψ := by rw [hψ]; exact hcomp.2
  apply Stacks.Sheaves.LocallyRingedSite.LocallyOnCovering.refine
    (fun {V} _ => Nonempty (GeneratorSections X L V))
    (Presheaf.imageSieve ψ (1 : X.O.obj.obj (Opposite.op U)))
    (Presheaf.imageSieve_mem X.J ψ _)
  intro V f hf
  obtain ⟨z, hz⟩ := hf
  have hz' : (pairingLinearMap X L N B V) z = 1 := by
    change (pairingLinearMap X L N B V) z =
      (X.O.obj.map f.op).hom 1 at hz
    simpa only [map_one] using hz
  obtain ⟨n, s, t, rfl⟩ := TensorProduct.exists_sum_tmul_eq z
  let s' : Fin (n + 1) → L.val.obj (Opposite.op V) := Fin.snoc s 0
  let t' : Fin (n + 1) → N.val.obj (Opposite.op V) := Fin.snoc t 0
  let a (i : Fin (n + 1)) : X.O.obj.obj (Opposite.op V) :=
    (pairingLinearMap X L N B V) (s' i ⊗ₜ t' i)
  have ha : ∑ i, (1 : X.O.obj.obj (Opposite.op V)) * a i = 1 := by
    simpa [a, s', t', Fin.sum_univ_castSucc, ← map_sum] using hz'
  have h := (Stacks.Sheaves.LocallyRingedSite.condition1_iff_condition2 X.O).mp hX.2
    V (n + 1) (Nat.succ_pos n) a ⟨fun _ => 1, ha⟩
  apply h.mono
  intro W g hg
  obtain ⟨i, hi⟩ := hg
  refine generatorSections_of_pairing_unit X L N B W
    (L.val.restrictₛₗ g.op (s' i)) (N.val.restrictₛₗ g.op (t' i)) ?_
  exact (pairing_restrict X L N B g (s' i) (t' i)).symm ▸ hi

/-- **Stacks Project, Tag 0B8Q**, the characterization clause. On a locally ringed site, a
sheaf of modules is invertible exactly when it is locally free of rank one. -/
@[stacks 0B8Q "characterization for locally ringed sites"]
theorem isInvertible_iff_isFiniteLocallyFreeOfRank_one
    (X : AlgebraicGeometry.RingedSite.{u, max u v, max u v})
    (L : SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X) :
    Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L ↔
      AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank X L 1 := by
  constructor
  · intro hL
    apply isFiniteLocallyFreeOfRank_one_of_exists_cover_localUnit
    intro U
    obtain ⟨S, hS, hne⟩ := exists_cover_generatorSections X L hX hL U
    refine ⟨S.arrows.category, fun g => g.obj.left, fun g => g.obj.hom, ?_, fun g => ?_⟩
    · rw [Sieve.ofArrows_category]
      exact hS
    · exact ⟨generatorSectionsIso X L g.obj.left
        (hne g.obj.hom g.property).some⟩
  · exact isInvertible_of_isFiniteLocallyFreeOfRank_one X L

private abbrev quadraticIdeal : Ideal (Zsqrtd (-5)) := Ideal.span {2, ⟨1, 1⟩}

private theorem quadraticIdeal_mul_self :
    quadraticIdeal * quadraticIdeal = Ideal.span {(2 : Zsqrtd (-5))} := by
  let b : Zsqrtd (-5) := ⟨1, 1⟩
  have h2 : (2 : Zsqrtd (-5)) ∈ quadraticIdeal := Ideal.subset_span (by simp)
  have hb : b ∈ quadraticIdeal := Ideal.subset_span (by simp [b])
  apply le_antisymm
  · rw [Ideal.span_mul_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨x, hx, y, hy, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Ideal.mem_span_singleton.mpr ⟨2, rfl⟩
    · exact Ideal.mem_span_singleton.mpr ⟨b, rfl⟩
    · exact Ideal.mem_span_singleton.mpr ⟨b, by change b * 2 = 2 * b; ring⟩
    · exact Ideal.mem_span_singleton.mpr
        ⟨⟨-2, 1⟩, by ext <;> norm_num [Zsqrtd.re_mul, Zsqrtd.im_mul]⟩
  · apply Ideal.span_le.mpr
    rintro _ (rfl : _ = (2 : Zsqrtd (-5)))
    have h4 := Ideal.mul_mem_mul h2 h2
    have h2b := Ideal.mul_mem_mul h2 hb
    have hbb := Ideal.mul_mem_mul hb hb
    have heq : (2 : Zsqrtd (-5)) = 2 * 2 + (2 * b - b * b) - 2 * 2 * 2 := by
      ext <;> norm_num [b, Zsqrtd.re_mul, Zsqrtd.im_mul]
    rw [heq]
    exact (quadraticIdeal * quadraticIdeal).sub_mem
      ((quadraticIdeal * quadraticIdeal).add_mem h4
        ((quadraticIdeal * quadraticIdeal).sub_mem h2b hbb))
      ((quadraticIdeal * quadraticIdeal).mul_mem_right 2 h4)

private theorem quadraticIdeal_not_principal : ¬quadraticIdeal.IsPrincipal := by
  intro hI
  let := hI
  let x := Submodule.IsPrincipal.generator quadraticIdeal
  have h2 : x ∣ (2 : Zsqrtd (-5)) :=
    (Submodule.IsPrincipal.mem_iff_generator_dvd _).mp (Ideal.subset_span (by simp))
  have hb : x ∣ (⟨1, 1⟩ : Zsqrtd (-5)) :=
    (Submodule.IsPrincipal.mem_iff_generator_dvd _).mp (Ideal.subset_span (by simp))
  have hn2 : x.norm ∣ 4 := by
    simpa [Zsqrtd.normMonoidHom, Zsqrtd.norm] using map_dvd Zsqrtd.normMonoidHom h2
  have hn6 : x.norm ∣ 6 := by
    simpa [Zsqrtd.normMonoidHom, Zsqrtd.norm] using map_dvd Zsqrtd.normMonoidHom hb
  have hn : x.norm ∣ 2 := by simpa using dvd_sub hn6 hn2
  have hnonneg : 0 ≤ x.norm := Zsqrtd.norm_nonneg (by norm_num) x
  have hone : x.norm = 1 := by
    have hle := Int.le_of_dvd (by norm_num : (0 : ℤ) < 2) hn
    have hnzero : x.norm ≠ 0 := by intro h; simp [h] at hn
    have him : x.im = 0 := by
      rw [Zsqrtd.norm_def] at hle
      nlinarith [sq_nonneg x.re, sq_nonneg x.im]
    have hre : -1 ≤ x.re ∧ x.re ≤ 1 := by
      rw [Zsqrtd.norm_def, him] at hle
      constructor <;> nlinarith
    have hre' : x.re = -1 ∨ x.re = 0 ∨ x.re = 1 := by omega
    rcases hre' with hr | hr | hr <;> simp_all [Zsqrtd.norm_def]
  have hxunit : IsUnit x := (Zsqrtd.norm_eq_one_iff' (by norm_num) x).mp hone
  have htop : quadraticIdeal = ⊤ := Ideal.eq_top_of_isUnit_mem _
    (Submodule.IsPrincipal.generator_mem _) hxunit
  let f : Zsqrtd (-5) →+* ZMod 2 := Zsqrtd.lift ⟨1, by decide⟩
  have hle : quadraticIdeal ≤ RingHom.ker f := by
    apply Ideal.span_le.mpr
    rintro z (rfl | rfl) <;> norm_num [RingHom.mem_ker, f, Zsqrtd.lift] <;> decide
  have h := hle (htop ▸ (show (1 : Zsqrtd (-5)) ∈ (⊤ : Ideal _) from trivial))
  simp [RingHom.mem_ker] at h

private theorem quadratic_two_regular : (2 : Zsqrtd (-5)) ∈ nonZeroDivisors _ := by
  rw [mem_nonZeroDivisors_iff]
  constructor <;> intro z hz <;> ext
  all_goals simp only [Zsqrtd.re_zero, Zsqrtd.im_zero]
  all_goals first
    | (have h := congrArg Zsqrtd.re hz; simp at h; omega)
    | (have h := congrArg Zsqrtd.im hz; simp at h; omega)


private theorem principal_of_linearEquiv {R : Type*} [CommRing R] (I : Ideal R)
    (e : I ≃ₗ[R] R) : I.IsPrincipal := by
  refine ⟨⟨(e.symm 1 : R), ?_⟩⟩
  change I = Ideal.span {(e.symm 1 : R)}
  apply le_antisymm
  · intro x hx
    apply Ideal.mem_span_singleton.mpr
    refine ⟨e ⟨x, hx⟩, ?_⟩
    have h := congrArg Subtype.val (e.symm.map_smul (e ⟨x, hx⟩) (1 : R))
    simpa [smul_eq_mul, mul_comm] using h
  · exact Ideal.span_le.mpr (by simp)

private theorem exists_invertible_nonprincipal_ideal :
    ∃ (R : Type w) (_ : CommRing R) (I : Ideal R),
      Module.Invertible R I ∧ ¬ I.IsPrincipal := by
  let R := ULift.{w} (Zsqrtd (-5))
  let e : Zsqrtd (-5) ≃+* R := ULift.ringEquiv.symm
  let I := Ideal.map e.toRingHom quadraticIdeal
  have hmul : I * I = Ideal.span {(2 : R)} := by
    rw [← Ideal.map_mul, quadraticIdeal_mul_self, Ideal.map_span, Set.image_singleton]
    rfl
  have hreg : (2 : R) ∈ nonZeroDivisors R := by
    rw [mem_nonZeroDivisors_iff]
    constructor <;> intro x hx
    all_goals
      apply e.symm.injective
      have heq := congrArg e.symm hx
      simp only [map_mul, map_ofNat, map_zero] at heq ⊢
      first
        | exact (mem_nonZeroDivisors_iff.mp quadratic_two_regular).1 _ heq
        | exact (mem_nonZeroDivisors_iff.mp quadratic_two_regular).2 _ heq
  refine ⟨R, inferInstance, I, Ideal.invertible_of_mul_eq_span_singleton hreg hmul, ?_⟩
  intro hI
  apply quadraticIdeal_not_principal
  have h := hI.map_ringHom e.symm.toRingHom
  have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id _ :=
    RingHom.ext (fun x => e.symm_apply_apply x)
  simpa only [I, Ideal.map_map, he, Ideal.map_id] using h

/-- **Stacks Project, Tag 0B8Q**, the parenthetical clause. Without local ringedness the
converse fails: there is a ringed site carrying an invertible sheaf of modules which is not
locally free of rank one. -/
@[stacks 0B8Q "the converse fails in general"]
theorem exists_isInvertible_not_isFiniteLocallyFreeOfRank_one :
    ∃ (X : AlgebraicGeometry.RingedSite.{u, v, w})
      (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
      Stacks.SheafOfModules.IsInvertible X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L ∧
        ¬ AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank X L 1 := by
  obtain ⟨R, hR, I, hI, hn⟩ := exists_invertible_nonprincipal_ideal.{w}
  let := hR
  let := hI
  apply exists_isInvertible_not_rank_one_of_module (CommRingCat.of R) (ModuleCat.of R I)
  rintro ⟨e⟩
  exact hn (principal_of_linearEquiv I e)

end AlgebraicGeometry.RingedSite

end
