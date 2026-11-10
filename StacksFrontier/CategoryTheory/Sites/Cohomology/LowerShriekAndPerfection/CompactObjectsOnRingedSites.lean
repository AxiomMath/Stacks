module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriekAndPerfection.SliceUnitModule
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelian
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.FromAGeneratingSet
import StacksCore.Tactic.StacksAttribute

/-!
# Compact objects on a ringed site with enough quasi-compact objects

Let `(C, O)` be a ringed site in which every object is covered by quasi-compact objects. Then
every compact object of the derived category of sheaves of `O`-modules is a direct summand of a
bounded complex each of whose terms is a finite direct sum of modules `j_{U!} O_U` with `U`
quasi-compact.

The proof is Stacks 094B applied to the set of the `j_{U!} O_U` for quasi-compact `U`. Two
things have to be checked about that set. It generates: a sheaf of modules `M` is covered by
the sum of one copy of `j_{U!} O_U` for each pair of a quasi-compact `U` and a section of `M`
over `U`, the corresponding map being the one named by
`Stacks.Sites.OverModules.extensionByZeroHomEquiv`, and this map is an epimorphism because the
covering hypothesis makes every section of the target locally of that form. And its members are
compact: morphisms out of `j_{U!} O_U` are the sections over `U`, by that same bijection, and
sections over a quasi-compact object commute with direct sums by Stacks 0935.

## Main results

* `Stacks.Cohomology.exists_retract_finiteComplex_extensionByZero_of_isCompactObject`: the
  statement above, Tag 094C.

## Implementation notes

A covering by quasi-compact objects is taken to be a pre-zero-hypercover whose covering sieve
belongs to the topology and whose source objects are all quasi-compact; that is the form in
which the separatedness argument uses it.

The module universe is `max u v w m` for a site with objects in `Type u`, morphisms in `Type v`
and ring sections in `Type w`, which is the smallest universe containing all three in which the
index set of the generating family — a sum over pairs `(U, s)` — lives. This is why the rank-one
module has to be the `ULift`ed `Stacks.Sites.OverModules.sheafUnit` rather than
`SheafOfModules.unit`.

The abelian structure on sheaves of modules is pinned with a local priority: the cohomology
imports bring in a second route to it, and the two are not syntactically equal, so the
statement of Stacks 094B would otherwise be elaborated against a different `Abelian` instance
than the one in the derived-category hypotheses.

## References

* [Stacks Project, Tag 094C](https://stacks.math.columbia.edu/tag/094C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sites.OverModules

namespace Stacks.Cohomology

universe u v w m

attribute [local instance] HasDerivedCategory.standard

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  [HasWeakSheafify X.J AddCommGrpCat.{max u v w m}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w m}]

/-- A cofan of abelian groups is a colimit exactly when the induced map out of the direct sum is
bijective: the direct sum is one such colimit, and the comparison with any other is an
isomorphism of abelian groups, hence bijective. -/
private lemma bijective_directSumDesc {ι : Type u} [DecidableEq ι]
    (E : ι → AddCommGrpCat.{max u v}) (c : Cofan E) (hc : IsColimit c) :
    Function.Bijective (DirectSum.toAddMonoid fun i => (c.inj i).hom) := by
  let d : Cofan E := Cofan.mk (AddCommGrpCat.of (DirectSum ι fun i => E i))
    (fun i => AddCommGrpCat.ofHom (DirectSum.of (fun i => E i) i))
  let hd : IsColimit d := Cofan.IsColimit.mk _
    (fun s => AddCommGrpCat.ofHom (DirectSum.toAddMonoid fun i => (s.inj i).hom))
    (fun s i => by
      ext x
      exact DirectSum.toAddMonoid_of (fun i => (s.inj i).hom) i x)
    (fun s f hf => AddCommGrpCat.hom_ext <| DirectSum.addHom_ext fun i x =>
      (ConcreteCategory.congr_hom (hf i) x).trans
        (DirectSum.toAddMonoid_of (fun i => (s.inj i).hom) i x).symm)
  let e := hd.coconePointUniqueUpToIso hc
  have he : e.hom.hom = DirectSum.toAddMonoid (fun i => (c.inj i).hom) :=
    DirectSum.addHom_ext fun i x =>
      (ConcreteCategory.congr_hom (hd.comp_coconePointUniqueUpToIso_hom hc ⟨i⟩) x).trans
        (DirectSum.toAddMonoid_of (fun i => (c.inj i).hom) i x).symm
  rw [← he]
  exact (ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance

/-- `j_{U!} O_U` is a compact object of the category of sheaves of modules when `U` is
quasi-compact: morphisms out of it are the sections over `U`, and those commute with direct
sums by Stacks 0935. -/
private lemma isCompactObject_extensionByZeroUnit (U : X.C)
    (hU : X.J.IsQuasiCompactObject U) :
    IsCompactObject.{max u v w m}
      (extensionByZeroUnit.{v, u, w, m} X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) := by
  constructor
  intro I _ E _
  let H := extensionByZeroUnit.{v, u, w, m} X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  let V := SheafOfModules.toSheaf.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
    (sheafSections X.J AddCommGrpCat.{max u v w m}).obj (op U)
  have : PreservesColimitsOfShape (Discrete I) V :=
    Stacks.Sites.sheafOfModules_sections_preserves_coproducts X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U hU I
  let c : Cofan (fun i => V.obj (E i)) :=
    Cofan.mk (V.obj (∐ E)) (fun i => V.map (Sigma.ι E i))
  have hc : IsColimit c := isColimitCofanMkObjOfIsColimit V E (Sigma.ι E)
    (coproductIsCoproduct E)
  let e :=
    extensionByZeroHomAddEquiv.{v, u, w, m} X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  let a := DirectSum.congrAddEquiv (fun i => e (E i))
  let φ := DirectSum.toAddMonoid (fun i => Preadditive.rightComp H (Sigma.ι E i))
  let ψ := DirectSum.toAddMonoid (fun i => (c.inj i).hom)
  have he : (e (∐ E)).toAddMonoidHom.comp φ = ψ.comp a.toAddMonoidHom := by
    apply DirectSum.addHom_ext
    intro i f
    change e (∐ E) (φ (DirectSum.of (fun i => H ⟶ E i) i f)) =
      ψ (a (DirectSum.of (fun i => H ⟶ E i) i f))
    rw [show φ (DirectSum.of (fun i => H ⟶ E i) i f) = f ≫ Sigma.ι E i from
      DirectSum.toAddMonoid_of (fun i => Preadditive.rightComp H (Sigma.ι E i)) i f]
    change extensionByZeroHomEquiv.{v, u, w, m} X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
      (∐ E) (f ≫ Sigma.ι E i) = _
    rw [extensionByZeroHomEquiv_naturality]
    change _ = ψ (DirectSum.map (fun i => (e (E i)).toAddMonoidHom)
      (DirectSum.of (fun i => H ⟶ E i) i f))
    rw [DirectSum.map_of]
    exact (DirectSum.toAddMonoid_of (fun i => (c.inj i).hom) i (e (E i) f)).symm
  have hb : Function.Bijective ((e (∐ E)).toAddMonoidHom.comp φ) := by
    rw [he]
    exact (bijective_directSumDesc _ c hc).comp a.bijective
  exact ⟨fun x y h => hb.1 (congrArg (e (∐ E)) h), fun f => by
    obtain ⟨x, hx⟩ := hb.2 (e (∐ E) f)
    exact ⟨x, (e (∐ E)).injective hx⟩⟩

/-- The modules `j_{U!} O_U` with `U` quasi-compact generate the sheaves of modules on a ringed
site all of whose objects are covered by quasi-compact ones: the sum over all pairs of a
quasi-compact `U` and a section of `M` over `U` surjects onto `M`, because the covering
hypothesis lets any two maps out of the sum that agree after composition be compared locally. -/
private lemma exists_epi_sigma_extensionByZeroUnit
    (hqc : ∀ U : X.C, ∃ 𝒰 : PreZeroHypercover.{max u v} U,
      𝒰.sieve₀ ∈ X.J U ∧ ∀ i, X.J.IsQuasiCompactObject (𝒰.X i))
    (M : SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    ∃ (I : Type (max u v w m))
      (E : I → SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
      (∀ i, E i ∈ Set.range fun U : {U : X.C // X.J.IsQuasiCompactObject U} =>
        extensionByZeroUnit.{v, u, w, m} X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U.1) ∧
      ∃ f : (∐ E) ⟶ M, Epi f := by
  classical
  let I : Type (max u v w m) :=
    Σ U : {U : X.C // X.J.IsQuasiCompactObject U}, M.val.obj (op U.1)
  let U : I → X.C := fun i => i.1.1
  let E : I → SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
    fun i => extensionByZeroUnit.{v, u, w, m} X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (U i)
  let fs : (i : I) → E i ⟶ M := fun i =>
    (extensionByZeroHomEquiv.{v, u, w, m} X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (U i) M).symm i.2
  let f : (∐ E) ⟶ M := Sigma.desc fs
  refine ⟨I, E, fun i => ⟨⟨U i, i.1.2⟩, rfl⟩, ⟨f, ⟨?_⟩⟩⟩
  intro N a b hab
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro X'
  ext x
  obtain ⟨𝒰, hcov, hqcU⟩ := hqc X'.unop
  let V : 𝒰.I₀ → X.C := 𝒰.X
  let g : (i : 𝒰.I₀) → V i ⟶ X'.unop := 𝒰.f
  have hg : Sieve.ofArrows V g ∈ X.J X'.unop := by
    simpa [V, g, PreZeroHypercover.sieve₀] using hcov
  have hN : Presheaf.IsSheaf X.J
      (N.val.presheaf ⋙ forget AddCommGrpCat.{max u v w m}) :=
    Presheaf.isSheaf_comp_of_isSheaf _ _ _ N.isSheaf
  apply (hN.isSheafFor (Sieve.ofArrows V g) hg).isSeparatedFor.ext
  intro Y' k hk
  obtain ⟨i, c, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hk
  let j : I := ⟨⟨V i, hqcU i⟩, (M.val.map (g i).op) x⟩
  have hleg : fs j ≫ a = fs j ≫ b := by
    have hf : Sigma.ι E j ≫ f = fs j := Sigma.ι_comp_desc _ _
    simpa only [← Category.assoc, hf] using congrArg (fun q => Sigma.ι E j ≫ q) hab
  have hlocal : (a.val.app (op (V i))) ((M.val.map (g i).op) x) =
      (b.val.app (op (V i))) ((M.val.map (g i).op) x) := by
    have h := congrArg (extensionByZeroHomEquiv.{v, u, w, m} X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (V i) N) hleg
    simp only [extensionByZeroHomEquiv_naturality, fs, U, j] at h
    convert h using 1 <;> congr 1 <;>
      exact ((extensionByZeroHomEquiv.{v, u, w, m} X.J
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (V i) M).apply_symm_apply _).symm
  rw [PresheafOfModules.naturality_apply a.val (g i).op x,
    PresheafOfModules.naturality_apply b.val (g i).op x] at hlocal
  rw [op_comp, Functor.map_comp]
  change (N.val.presheaf.map c.op).hom ((N.val.presheaf.map (g i).op).hom _) = _
  exact congrArg (N.val.presheaf.map c.op).hom hlocal

-- Keep the accepted statement's abelian instance despite the additional cohomology imports.
attribute [local instance 1100] AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules

/-- **Stacks 094C.** On a ringed site every object of which is covered by quasi-compact objects,
a compact object of the derived category of sheaves of modules is a direct summand of a bounded
complex whose terms are finite direct sums of the modules `j_{U!} O_U` for quasi-compact `U`. -/
@[stacks 094C]
public theorem exists_retract_finiteComplex_extensionByZero_of_isCompactObject
    (hqc : ∀ U : X.C, ∃ 𝒰 : PreZeroHypercover.{max u v} U,
      𝒰.sieve₀ ∈ X.J U ∧ ∀ i, X.J.IsQuasiCompactObject (𝒰.X i))
    (K : DerivedCategory
      (SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [IsCompactObject.{max u v w m} K] :
    ∃ (L : CochainComplex
        (SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
      (a b : ℤ),
      L.IsStrictlyGE a ∧ L.IsStrictlyLE b ∧
      (∀ i : ℤ, ∃ (n : ℕ) (U : Fin n → X.C),
        (∀ j, X.J.IsQuasiCompactObject (U j)) ∧
        Nonempty (L.X i ≅ ∐ fun j : Fin n ↦
          extensionByZeroUnit.{v, u, w, m} X.J
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (U j))) ∧
      Nonempty (Retract K (DerivedCategory.Q.obj L)) := by
  let generators :
      Set (SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Set.range fun U : {U : X.C // X.J.IsQuasiCompactObject U} =>
      extensionByZeroUnit.{v, u, w, m} X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U.1
  have hcompact : ∀ E ∈ generators, IsCompactObject.{max u v w m} E := by
    rintro E ⟨⟨U, hU⟩, rfl⟩
    exact isCompactObject_extensionByZeroUnit.{u, v, w, m} X U hU
  let _ : IsGrothendieckAbelian.{max u v w m}
      (SheafOfModules.{max u v w m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    Stacks.SheafOfModules.sheafModulesGrothendieck.{u, v, w, m} X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  obtain ⟨L, a, b, hGE, hLE, hterms, hret⟩ :=
    Stacks.Cohomology.CompactObjects.exists_retract_finiteComplex_of_isCompactObject generators
      (exists_epi_sigma_extensionByZeroUnit.{u, v, w, m} X hqc) hcompact K
  refine ⟨L, a, b, hGE, hLE, fun i => ?_, hret⟩
  obtain ⟨n, E, hE, ⟨hL⟩⟩ := hterms i
  choose W hW using fun j => Set.mem_range.mp (hE j)
  exact ⟨n, fun j => (W j).1, fun j => (W j).2,
    ⟨hL.trans (eqToIso (congrArg (fun F : Fin n → _ => ∐ F) (funext fun j => (hW j).symm)))⟩⟩

end Stacks.Cohomology

end
