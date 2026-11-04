module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Presentable.Directed
public meta import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Criteria
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Defs
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.JacobiZariski
public import StacksFrontier.RingTheory.CompleteIntersection.Smooth
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Henselian.HenselizationUniversalProperty
public import StacksFrontier.RingTheory.Henselian.Pair.Henselization
public import StacksFrontier.RingTheory.Henselian.StrictHenselization
public import StacksFrontier.RingTheory.Kaehler.JacobiZariski
public import StacksFrontier.RingTheory.NaiveCotangent.Defs

@[expose] public section


/-!
# The naive cotangent complex and henselization

For a commutative square of ring maps `A → B`, `A' → B'`, base change gives a canonical
map from the naive cotangent complex of `B` over `A`, tensored with `B'`, to the naive
cotangent complex of `B'` over `A'`. If both vertical maps are filtered colimits of étale
maps, this comparison induces isomorphisms on all homology groups. Henselization and strict
henselization of a local ring are such filtered colimits, so the comparison map is a
quasi-isomorphism for a local homomorphism of local rings passed to henselizations or to
strict henselizations.

## Main definitions

* `Algebra.naiveCotangentComplexBaseChange` is the termwise base change of a naive cotangent
  complex.
* `Algebra.naiveCotangentComplexBaseChangeComparison` is the canonical comparison map associated
  to a commutative square of rings.

## Main results

* `Algebra.quasiIso_baseChangeComparison_of_ind_etale` is the comparison for a square whose two
  vertical maps are filtered colimits of étale maps. It is the engine of Stacks 0D08, and is
  stated at that generality because the source's proof uses nothing else about the
  henselizations it is stated for.
* `Algebra.naiveCotangentComplex_quasiIso_henselization_and_strictHenselization`
  gives the two quasi-isomorphisms for henselizations and strict henselizations.
* `Algebra.naiveCotangentComplex_quasiIso_henselizationPair` gives the quasi-isomorphism for the
  henselization of a pair, which is the instance of Stacks 0D08 that Stacks 0DZC appeals to.

## Implementation notes

Henselizations and strict henselizations are represented by `IsLocalRing.IsHenselization`;
`IsLocalRing.IsHenselization.ind_etale` is the bridge from this representation to the source's
filtered colimits of étale algebras. The algebra structure `Aʰ → Bʰ`, together with its
locality, characterizes the canonical induced map by
`HenselianLocalRing.indEtaleAlgHom_unique`, which is Stacks tag 04GS. For strict
henselizations, the compatible map of residue fields and its induced-map equation characterize
`Aˢʰ → Bˢʰ` by
`HenselianLocalRing.indEtaleAlgHomOfResidue_unique`, Stacks tag 04GU.

The base-changed complex is presented directly as the two-term complex obtained by base changing
the canonical conormal map. Thus its terms are literally `B' ⊗[B] (-)`, which is the tensor
product complex in the source.

Injectivity of the conormal comparison map along a filtered colimit of étale maps is imported
from `RingHom.cotangentMap_toComp_injective_of_isFilteredColimit_isLocalCompleteIntersection`,
applied through `RingHom.syntomic_iff_flat_and_isLocalCompleteIntersection` to see an étale map
as a local complete intersection.

## References

* [Stacks Project, Tag 0D08](https://stacks.math.columbia.edu/tag/0D08)
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex TensorProduct

universe u v w

/-! ## Support declarations

`CommAlgCat.flat_of_ind_etale` and the filtered-colimit representability lemmas it rests on now
come from `StacksFrontier.RingTheory.Henselian.Henselization.Defs`, which has been revised to carry
them; the private replays that stood here pending that promotion are gone. That revision also
places `Rh` in its own universe and states the `ind_etale` field on `ULift Rh`, so the colimit
condition is taken through `IsHenselization.ind_etale_of_universe_le` rather than from the field
directly.
-/

namespace Algebra

/-- The naive cotangent complex `NL_{B/A}` after termwise extension of scalars from `B` to `B'`.
Its differential is the base change of the canonical conormal map. -/
public noncomputable def naiveCotangentComplexBaseChange
    (A : Type u) (B B' : Type v) [CommRing A] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra B B'] : ChainComplex (ModuleCat.{max u v} B') ℕ :=
  HomologicalComplex.double
    (ModuleCat.ofHom ((Generators.self A B).toExtension.cotangentComplex.baseChange B'))
    (show (ComplexShape.down ℕ).Rel 1 0 from rfl)

/-- The canonical map
`NL_{B/A} ⊗_B B' ⟶ NL_{B'/A'}` associated to a commutative square of rings. -/
public noncomputable def naiveCotangentComplexBaseChangeComparison
    (A A' : Type u) (B B' : Type v)
    [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A A'] [Algebra B B'] [Algebra A' B'] [Algebra A B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] :
    naiveCotangentComplexBaseChange A B B' ⟶
      HomologicalComplex.double
        (ModuleCat.ofHom (Generators.self A' B').toExtension.cotangentComplex)
        (show (ComplexShape.down ℕ).Rel 1 0 from rfl) :=
  let f : (Generators.self A B).toExtension.Hom
      (Generators.self A' B').toExtension :=
    (Generators.defaultHom (Generators.self A B) (Generators.self A' B')).toExtensionHom
  let f₁ : (Generators.self A B).toExtension.Cotangent →ₗ[B]
      (Generators.self A' B').toExtension.Cotangent := Extension.Cotangent.map f
  let f₀ : (Generators.self A B).toExtension.CotangentSpace →ₗ[B]
      (Generators.self A' B').toExtension.CotangentSpace := Extension.CotangentSpace.map f
  let d' := ModuleCat.ofHom
    (Generators.self A' B').toExtension.cotangentComplex
  let hrel : (ComplexShape.down ℕ).Rel 1 0 := rfl
  let hne : (1 : ℕ) ≠ 0 := by omega
  HomologicalComplex.mkHomFromDouble
    hrel hne
    (ModuleCat.ofHom (R := B') (f₁.liftBaseChange B') ≫
      (HomologicalComplex.doubleXIso₀ d' hrel).inv)
    (ModuleCat.ofHom (R := B') (f₀.liftBaseChange B') ≫
      (HomologicalComplex.doubleXIso₁ d' hrel hne).inv)
    (by
      dsimp only [d']
      rw [HomologicalComplex.double_d (hi₀₁ := hrel) (h := hne)]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      simp only [← Category.assoc]
      apply (cancel_mono
        (HomologicalComplex.doubleXIso₁
          (ModuleCat.ofHom (Generators.self A' B').toExtension.cotangentComplex)
          hrel hne).inv).2
      apply ModuleCat.hom_ext
      ext x
      change (Generators.self A' B').toExtension.cotangentComplex
          (f₁.liftBaseChange B' (1 ⊗ₜ[B] x)) =
        f₀.liftBaseChange B'
          ((Generators.self A B).toExtension.cotangentComplex.baseChange B' (1 ⊗ₜ[B] x))
      simp only [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, one_smul]
      rw [Extension.CotangentSpace.map_cotangentComplex])
    (by simp)

private theorem formallyEtale_of_ind_etale
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h : (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R S)) :
    Algebra.FormallyEtale R S := by
  classical
  obtain ⟨J, _, _, p, hp⟩ := h
  apply Algebra.FormallyEtale.iff_comp_bijective.mpr
  intro T _ _ I hI
  have he (j : J) : Algebra.FormallyEtale R (p.diag.obj j) := by
    have : Algebra.Etale R (p.diag.obj j) := hp j
    infer_instance
  refine ⟨fun f g hfg => ?_, fun f => ?_⟩
  · suffices e : CommAlgCat.ofHom f = CommAlgCat.ofHom g from
      congrArg CommAlgCat.Hom.hom e
    refine p.isColimit.hom_ext fun j => CommAlgCat.hom_ext ?_
    apply (Algebra.FormallyEtale.comp_bijective R (p.diag.obj j) I hI).injective
    change (Ideal.Quotient.mkₐ R I).comp (f.comp (p.ι.app j).hom) =
      (Ideal.Quotient.mkₐ R I).comp (g.comp (p.ι.app j).hom)
    rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, hfg]
  · choose l hl using fun j =>
      (Algebra.FormallyEtale.comp_bijective R (p.diag.obj j) I hI).surjective
        (f.comp (p.ι.app j).hom)
    let c : Cocone p.diag :=
      { pt := CommAlgCat.of R T
        ι.app j := CommAlgCat.ofHom (l j)
        ι.naturality i j a := by
          apply CommAlgCat.hom_ext
          apply (Algebra.FormallyEtale.comp_bijective R (p.diag.obj i) I hI).injective
          change (Ideal.Quotient.mkₐ R I).comp ((l j).comp (p.diag.map a).hom) =
            (Ideal.Quotient.mkₐ R I).comp (l i)
          rw [← AlgHom.comp_assoc, hl, hl, AlgHom.comp_assoc]
          congr 1
          exact congrArg CommAlgCat.Hom.hom (p.w a) }
    refine ⟨(p.isColimit.desc c).hom, ?_⟩
    suffices e : p.isColimit.desc c ≫ CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I) =
        CommAlgCat.ofHom f from congrArg CommAlgCat.Hom.hom e
    refine p.isColimit.hom_ext fun j => ?_
    change p.ι.app j ≫ p.isColimit.desc c ≫ CommAlgCat.ofHom (Ideal.Quotient.mkₐ R I) = _
    rw [← Category.assoc, p.isColimit.fac]
    exact CommAlgCat.hom_ext (hl j)

/-- An étale ring homomorphism is a local complete intersection homomorphism: an étale algebra is
smooth, hence syntomic, and a syntomic ring map is flat and a local complete intersection. -/
public theorem isLocalCompleteIntersection_of_etale
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : f.Etale) :
    RingHom.IsLocalCompleteIntersection f := by
  let := f.toAlgebra
  have : Algebra.Etale R S := hf
  have hs : Algebra.Syntomic R S :=
    { isLocalCompleteIntersection_fiber := fun p _ =>
        isLocalCompleteIntersection_of_smooth p.ResidueField (p.Fiber S) }
  exact ((RingHom.syntomic_iff_flat_and_isLocalCompleteIntersection f).mp hs).2

private theorem exists_ringEquiv_directLimit
    {J : Type v} [Preorder J] (F : J ⥤ CommRingCat.{v})
    (c : Cocone F) (hc : IsColimit c) :
    ∃ e : Ring.DirectLimit (fun j => F.obj j)
        (fun _ _ h => (F.map (homOfLE h)).hom) ≃+* c.pt,
      ∀ j x, e (Ring.DirectLimit.of (fun j => F.obj j)
        (fun _ _ h => (F.map (homOfLE h)).hom) j x) = (c.ι.app j).hom x := by
  let D : J → Type v := fun j => F.obj j
  let t : ∀ i j, i ≤ j → D i → D j :=
    fun i j h => (F.map (homOfLE h)).hom
  let d : Cocone F :=
    { pt := CommRingCat.of (Ring.DirectLimit D t)
      ι.app j := CommRingCat.ofHom (Ring.DirectLimit.of D t j)
      ι.naturality i j h := by
        ext x
        exact Ring.DirectLimit.of_f (G := D) (f := t) (leOfHom h) x }
  let hd : IsColimit d :=
    { desc s := CommRingCat.ofHom (Ring.DirectLimit.lift D t s.pt
        (fun j => (s.ι.app j).hom)
        (fun i j h x => congrArg (fun f => f.hom x) (s.w (homOfLE h))))
      fac s j := by
        ext x
        exact Ring.DirectLimit.lift_of (G := D) (f := t) s.pt
          (fun j => (s.ι.app j).hom)
          (fun i j h x => congrArg (fun f => f.hom x) (s.w (homOfLE h))) j x
      uniq s m hm := CommRingCat.hom_ext <| Ring.DirectLimit.hom_ext _ fun j => RingHom.ext fun x =>
        (congrArg (fun f => f.hom x) (hm j)).trans
          (Ring.DirectLimit.lift_of (G := D) (f := t) s.pt
          (fun j => (s.ι.app j).hom)
          (fun i j h x => congrArg (fun f => f.hom x) (s.w (homOfLE h))) j x).symm }
  exact ⟨(hd.coconePointUniqueUpToIso hc).commRingCatIsoToRingEquiv,
    fun j x => congrArg (fun f => f.hom x) (hd.fac c j)⟩

private theorem cotangentMap_toComp_injective_of_ind_etale
    {A : Type u} {B C : Type v} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    {S T : Type*} (α : Algebra.Generators A B S) (β : Algebra.Generators B C T)
    (h : (CommAlgCat.etale.{v} B).ind.{v} (CommAlgCat.of B C)) :
    Function.Injective
      ((Algebra.Extension.Cotangent.map (β.toComp α).toExtensionHom).liftBaseChange C) := by
  classical
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ :=
    CommAlgCat.ind_etale_iff_ind_algebraMap.mp h
  obtain ⟨I, _, _, _, F, _⟩ := IsFiltered.exists_directed J
  have : IsConnected I := IsFiltered.isConnected I
  let p : ColimitPresentation J (CommRingCat.of C) := ⟨D, s, hs⟩
  let q := p.reindex F
  let sys : RingMapSystemUnbundled.{v} I :=
    { R := fun _ => B
      S := fun i => q.diag.obj i
      commRingR := fun _ => inferInstance
      commRingS := fun _ => inferInstance
      fR := fun {_ _} _ => RingHom.id B
      fS := fun {_ _} h => (q.diag.map (homOfLE h)).hom
      fR_id := fun _ _ => rfl
      fR_comp := fun {_ _ _} _ _ _ => rfl
      fS_id := fun i x => by
        change (q.diag.map (𝟙 i)).hom x = x
        simp
      fS_comp := fun {_ _ _} hij hjk x => by
        change (q.diag.map (homOfLE hjk)).hom ((q.diag.map (homOfLE hij)).hom x) =
          (q.diag.map (homOfLE (hij.trans hjk))).hom x
        exact congrArg (fun f => f.hom x)
          (q.diag.map_comp (homOfLE hij) (homOfLE hjk)).symm
      g := fun i => (t.app (F.obj i)).hom
      square := fun {_ _} h x => congrArg (fun f => f.hom x)
        ((t.naturality (F.map (homOfLE h))).symm.trans (Category.id_comp _)) }
  obtain ⟨eB, heB⟩ := exists_ringEquiv_directLimit
    ((Functor.const I).obj (CommRingCat.of B))
    (constCocone I (CommRingCat.of B)) (isColimitConstCocone I (CommRingCat.of B))
  obtain ⟨eC, heC⟩ := exists_ringEquiv_directLimit q.diag q.cocone q.isColimit
  apply RingHom.cotangentMap_toComp_injective_of_isFilteredColimit_isLocalCompleteIntersection
    α β sys eB eC
  · apply Ring.DirectLimit.hom_ext
    intro i
    ext x
    change eC (sys.gInf (Ring.DirectLimit.of _ _ i x)) =
      algebraMap B C (eB (Ring.DirectLimit.of _ _ i x))
    calc
      _ = eC (sys.toSinf i (sys.g i x)) := congrArg eC (sys.toSinf_g i x).symm
      _ = (s.app (F.obj i)).hom ((t.app (F.obj i)).hom x) := heC i _
      _ = algebraMap B C x := congrArg (fun f => f.hom x) (hts (F.obj i)).2
      _ = _ := congrArg (algebraMap B C) (heB i x).symm
  · intro i
    exact isLocalCompleteIntersection_of_etale _ (hts (F.obj i)).1

/-- If `C` is a filtered colimit of étale `B`-algebras, then base change along `B → C` is an
isomorphism on first cotangent homology: `C ⊗[B] H₁(L_{B/A}) → H₁(L_{C/A})` is bijective.

Flatness of `C` over `B` reduces injectivity to injectivity of the conormal comparison map
along the ind-étale map, and surjectivity is the Jacobi–Zariski exact sequence together with
the vanishing of `H₁(L_{C/B})` for a formally étale `B → C`. -/
public theorem h1Cotangent_liftBaseChange_bijective_of_ind_etale
    (A : Type u) (B C : Type v) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (h : (CommAlgCat.etale.{v} B).ind.{v} (CommAlgCat.of B C)) :
    Function.Bijective ((H1Cotangent.map A A B C).liftBaseChange C) := by
  have : Module.Flat B C := CommAlgCat.flat_of_ind_etale h
  have : FormallyEtale B C := formallyEtale_of_ind_etale h
  refine ⟨?_, fun y => (H1Cotangent.exact_liftBaseChange_map_of_flat A B C y).mp
    (Subsingleton.elim _ _)⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  let P := Generators.self A B
  let Q := Generators.self B C
  let W := Generators.self A C
  let f := (Generators.defaultHom P W).toExtensionHom
  let g := (Generators.defaultHom W (Q.comp P)).toExtensionHom
  have heq :
      (Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange C ∘ₗ
          P.toExtension.h1Cotangentι.baseChange C =
        (Q.comp P).toExtension.h1Cotangentι ∘ₗ Extension.H1Cotangent.map g ∘ₗ
          (Extension.H1Cotangent.map f).liftBaseChange C := by
    apply AlgebraTensorModule.ext
    intro a y
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul,
      LinearMap.liftBaseChange_tmul, map_smul]
    change a • Extension.h1Cotangentι (Extension.H1Cotangent.map _ y) =
      a • Extension.h1Cotangentι (Extension.H1Cotangent.map g (Extension.H1Cotangent.map f y))
    rw [← Extension.H1Cotangent.map_comp_apply, Extension.H1Cotangent.map_eq]
  apply Module.Flat.lTensor_preserves_injective_linearMap
    P.toExtension.h1Cotangentι Extension.h1Cotangentι_injective
  apply cotangentMap_toComp_injective_of_ind_etale P Q h
  change ((Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange C ∘ₗ
    P.toExtension.h1Cotangentι.baseChange C) x = _
  rw [map_zero, heq]
  change (Q.comp P).toExtension.h1Cotangentι
    (Extension.H1Cotangent.map g (((H1Cotangent.map A A B C).liftBaseChange C) x)) = 0
  rw [hx, map_zero, map_zero]

private theorem h1Cotangent_map_bijective_of_formallyEtale
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [FormallyEtale A B] : Function.Bijective (H1Cotangent.map A B C C) := by
  let P := Generators.self A B
  let Q := Generators.self B C
  let W := Generators.self A C
  have hd : Function.Bijective P.toExtension.cotangentComplex :=
    ⟨(Extension.subsingleton_h1Cotangent P.toExtension).mp inferInstance,
      fun y => (P.toExtension.exact_cotangentComplex_toKaehler y).mp
        (Subsingleton.elim _ _)⟩
  have hd' : LinearMap.ker (P.toExtension.cotangentComplex.baseChange C) = ⊥ :=
    LinearMap.ker_eq_bot.mpr ((LinearEquiv.ofBijective _ hd).baseChange B C).injective
  have hinj : Function.Injective (Extension.H1Cotangent.map (Q.ofComp P).toExtensionHom) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hx' : x.val ∈ LinearMap.ker (Q.comp P).toExtension.cotangentComplex ⊓
        LinearMap.ker (Extension.Cotangent.map (Q.ofComp P).toExtensionHom) :=
      ⟨x.property, congrArg Subtype.val hx⟩
    rw [← Generators.Cotangent.map_ker_baseChange_cotangentComplex Q P,
      hd', Submodule.map_bot, Submodule.mem_bot] at hx'
    exact Subtype.ext hx'
  refine ⟨?_, fun y => (H1Cotangent.exact_map_δ A B C y).mp (Subsingleton.elim _ _)⟩
  have hi := hinj.comp (Generators.H1Cotangent.equiv W (Q.comp P)).injective
  convert hi using 1
  funext x
  change Extension.H1Cotangent.map _ x =
    Extension.H1Cotangent.map _ (Extension.H1Cotangent.map _ x)
  rw [← Extension.H1Cotangent.map_comp_apply, Extension.H1Cotangent.map_eq]

private theorem h1Cotangent_liftBaseChange_bijective_of_ind_etale_square
    (A A' : Type u) (B B' : Type v) [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra B B'] [Algebra A' B'] [Algebra A B']
    [IsScalarTower A B B'] [IsScalarTower A A' B']
    (hA : (CommAlgCat.etale.{u} A).ind.{u} (CommAlgCat.of A A'))
    (hB : (CommAlgCat.etale.{v} B).ind.{v} (CommAlgCat.of B B')) :
    Function.Bijective ((H1Cotangent.map A A' B B').liftBaseChange B') := by
  have : FormallyEtale A A' := formallyEtale_of_ind_etale hA
  have heq : (H1Cotangent.map A A' B B').liftBaseChange B' =
      H1Cotangent.map A A' B' B' ∘ₗ (H1Cotangent.map A A B B').liftBaseChange B' := by
    apply AlgebraTensorModule.ext
    intro a x
    simp only [LinearMap.comp_apply, LinearMap.liftBaseChange_tmul, map_smul]
    unfold H1Cotangent.map
    rw [← Extension.H1Cotangent.map_comp_apply, Extension.H1Cotangent.map_eq]
  rw [heq]
  exact (h1Cotangent_map_bijective_of_formallyEtale A A' B').comp
    (h1Cotangent_liftBaseChange_bijective_of_ind_etale A B B' hB)

private theorem kaehlerDifferential_map_bijective_of_formallyUnramified
    (A A' B : Type*) [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A B] [Algebra A' B] [IsScalarTower A A' B]
    [FormallyUnramified A A'] :
    Function.Bijective (KaehlerDifferential.map A A' B B) := by
  refine ⟨?_, KaehlerDifferential.map_surjective A A' B⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map A A' B x).mp hx
  rw [Subsingleton.elim y 0, map_zero]

@[ega "0 20.5.8" "more general", ega "0 20.7.7" "special case"]
private theorem kaehlerDifferential_liftBaseChange_bijective_of_formallyEtale
    (A A' B B' : Type*) [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra B B'] [Algebra A' B'] [Algebra A B']
    [IsScalarTower A B B'] [IsScalarTower A A' B']
    [FormallyUnramified A A'] [FormallyEtale B B'] :
    Function.Bijective ((KaehlerDifferential.map A A' B B').liftBaseChange B') := by
  have heq : (KaehlerDifferential.map A A' B B').liftBaseChange B' =
      KaehlerDifferential.map A A' B' B' ∘ₗ KaehlerDifferential.mapBaseChange A B B' := by
    ext x
    simp [KaehlerDifferential.map_D, KaehlerDifferential.mapBaseChange_tmul]
  rw [heq]
  exact (kaehlerDifferential_map_bijective_of_formallyUnramified A A' B').comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A B B').bijective

private theorem toKaehler_map_tmul_D
    {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra B B'] [Algebra A' B'] [Algebra A B']
    [IsScalarTower A B B'] [IsScalarTower A A' B']
    (P : Extension A B) (Q : Extension A' B') (f : P.Hom Q) (x : B) (y : P.Ring) :
    Q.toKaehler ((Extension.CotangentSpace.map f)
        (x ⊗ₜ[P.Ring] KaehlerDifferential.D A P.Ring y)) =
      (KaehlerDifferential.map A A' B B')
        (P.toKaehler (x ⊗ₜ[P.Ring] KaehlerDifferential.D A P.Ring y)) := by
  rw [Extension.CotangentSpace.map_tmul]
  simp only [Extension.toKaehler, KaehlerDifferential.mapBaseChange_tmul,
    KaehlerDifferential.map_D, Extension.Hom.toAlgHom_apply,
    Extension.Hom.algebraMap_toRingHom, map_smul, algebraMap_smul]

private theorem quasiIso_of_kernel_map
    {R : Type*} [Ring R] {S T : ShortComplex (ModuleCat.{v} R)} (φ : S ⟶ T)
    (hS : S.f = 0) (hT : T.f = 0) {H H' : ModuleCat.{v} R}
    (i : H ⟶ S.X₂) (i' : H' ⟶ T.X₂)
    (hi : Function.Exact i.hom S.g.hom) (hi' : Function.Exact i'.hom T.g.hom)
    (hinj : Function.Injective i.hom) (hinj' : Function.Injective i'.hom)
    (f : H ⟶ H') (hf : Function.Bijective f.hom) (hc : i ≫ φ.τ₂ = f ≫ i') :
    ShortComplex.QuasiIso φ := by
  let d := ShortComplex.RightHomologyMapData.ofIsLimitKernelFork φ
    hS _ (ModuleCat.isLimitKernelFork i S.g hi hinj)
    hT _ (ModuleCat.isLimitKernelFork i' T.g hi' hinj') f hc
  rw [d.quasiIso_iff]
  exact (LinearEquiv.ofBijective f.hom hf).toModuleIso.isIso_hom

private theorem quasiIso_of_cokernel_map
    {R : Type*} [Ring R] {S T : ShortComplex (ModuleCat.{v} R)} (φ : S ⟶ T)
    (hS : S.g = 0) (hT : T.g = 0) {H H' : ModuleCat.{v} R}
    (q : S.X₂ ⟶ H) (q' : T.X₂ ⟶ H')
    (hq : Function.Exact S.f.hom q.hom) (hq' : Function.Exact T.f.hom q'.hom)
    (hsurj : Function.Surjective q.hom) (hsurj' : Function.Surjective q'.hom)
    (f : H ⟶ H') (hf : Function.Bijective f.hom) (hc : φ.τ₂ ≫ q' = q ≫ f) :
    ShortComplex.QuasiIso φ := by
  let d := ShortComplex.RightHomologyMapData.ofIsColimitCokernelCofork φ
    hS _ (ModuleCat.isColimitCokernelCofork S.f q hq hsurj)
    hT _ (ModuleCat.isColimitCokernelCofork T.f q' hq' hsurj') f hc
  rw [d.quasiIso_iff]
  exact (LinearEquiv.ofBijective f.hom hf).toModuleIso.isIso_hom

private theorem exact_double_left {R : Type*} [Ring R] {H M N : ModuleCat.{v} R}
    (i : H ⟶ M) (d : M ⟶ N) (h : Function.Exact i.hom d.hom) :
    Function.Exact
      (i ≫ (doubleXIso₀ d (show (ComplexShape.down ℕ).Rel 1 0 from rfl)).inv).hom
      ((double d (show (ComplexShape.down ℕ).Rel 1 0 from rfl)).d 1 0).hom := by
  rw [double_d _ _ (by omega)]
  change Function.Exact
    ((doubleXIso₀ d _).toLinearEquiv.symm.toLinearMap ∘ₗ i.hom)
    ((doubleXIso₁ d _ _).toLinearEquiv.symm.toLinearMap ∘ₗ
      (d.hom ∘ₗ (doubleXIso₀ d _).toLinearEquiv.toLinearMap))
  rw [LinearEquiv.postcomp_exact_iff_exact, LinearEquiv.conj_symm_exact_iff_exact]
  exact h

private theorem exact_double_right {R : Type*} [Ring R] {H M N : ModuleCat.{v} R}
    (d : M ⟶ N) (q : N ⟶ H) (h : Function.Exact d.hom q.hom) :
    Function.Exact
      ((double d (show (ComplexShape.down ℕ).Rel 1 0 from rfl)).d 1 0).hom
      ((doubleXIso₁ d (show (ComplexShape.down ℕ).Rel 1 0 from rfl) (by omega)).hom ≫ q).hom := by
  rw [double_d _ _ (by omega)]
  change Function.Exact
    (((doubleXIso₁ d _ _).toLinearEquiv.symm.toLinearMap ∘ₗ d.hom) ∘ₗ
      (doubleXIso₀ d _).toLinearEquiv.toLinearMap)
    (q.hom ∘ₗ (doubleXIso₁ d _ _).toLinearEquiv.toLinearMap)
  rw [LinearEquiv.precomp_exact_iff_exact, LinearEquiv.conj_symm_exact_iff_exact]
  exact h

private theorem quasiIso_baseChangeComparison_of_bijective
    (A A' : Type u) (B B' : Type v) [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra B B'] [Algebra A' B'] [Algebra A B']
    [IsScalarTower A B B'] [IsScalarTower A A' B'] [Module.Flat B B']
    (h₁ : Function.Bijective ((H1Cotangent.map A A' B B').liftBaseChange B'))
    (h₀ : Function.Bijective ((KaehlerDifferential.map A A' B B').liftBaseChange B')) :
    QuasiIso (naiveCotangentComplexBaseChangeComparison A A' B B') := by
  let P := (Generators.self A B).toExtension
  let Q := (Generators.self A' B').toExtension
  let f := (Generators.defaultHom (Generators.self A B) (Generators.self A' B')).toExtensionHom
  let d := ModuleCat.ofHom (P.cotangentComplex.baseChange B')
  let d' := ModuleCat.ofHom Q.cotangentComplex
  let hrel : (ComplexShape.down ℕ).Rel 1 0 := rfl
  let hn : (1 : ℕ) ≠ 0 := by omega
  let K := double d hrel
  let L := double d' hrel
  let φ : K ⟶ L := naiveCotangentComplexBaseChangeComparison A A' B B'
  let e₁ := doubleXIso₀ d hrel
  let e₀ := doubleXIso₁ d hrel hn
  let e₁' := doubleXIso₀ d' hrel
  let e₀' := doubleXIso₁ d' hrel hn
  have hφ₁ : φ.f 1 = e₁.hom ≫ ModuleCat.ofHom
      ((Extension.Cotangent.map f).liftBaseChange B') ≫ e₁'.inv := by
    dsimp only [φ, naiveCotangentComplexBaseChangeComparison]
    erw [mkHomFromDouble_f₀]
  have hφ₀ : φ.f 0 = e₀.hom ≫ ModuleCat.ofHom
      ((Extension.CotangentSpace.map f).liftBaseChange B') ≫ e₀'.inv := by
    dsimp only [φ, naiveCotangentComplexBaseChangeComparison]
    erw [mkHomFromDouble_f₁]
  change QuasiIso φ
  rw [quasiIso_iff]
  intro n
  rcases n with _ | (_ | n)
  · rw [ChainComplex.quasiIsoAt₀_iff]
    let eH : (B' ⊗[B] Ω[B⁄A]) ≃ₗ[B'] ULift.{u} (B' ⊗[B] Ω[B⁄A]) :=
      ULift.moduleEquiv.symm
    let eH' : Ω[B'⁄A'] ≃ₗ[B'] ULift.{u} Ω[B'⁄A'] := ULift.moduleEquiv.symm
    let q := e₀.hom ≫ ModuleCat.ofHom (eH.toLinearMap ∘ₗ P.toKaehler.baseChange B')
    let q' := e₀'.hom ≫ ModuleCat.ofHom (eH'.toLinearMap ∘ₗ Q.toKaehler)
    refine quasiIso_of_cokernel_map _
      (double_d_eq_zero₀ d hrel 0 0 (by omega))
      (double_d_eq_zero₀ d' hrel 0 0 (by omega)) q q'
      (exact_double_right d (ModuleCat.ofHom (eH.toLinearMap ∘ₗ P.toKaehler.baseChange B'))
        (LinearEquiv.postcomp_exact_iff_exact.mpr
          (Module.Flat.lTensor_exact B' P.exact_cotangentComplex_toKaehler)))
      (exact_double_right d' (ModuleCat.ofHom (eH'.toLinearMap ∘ₗ Q.toKaehler))
        (LinearEquiv.postcomp_exact_iff_exact.mpr Q.exact_cotangentComplex_toKaehler))
      ((eH.surjective.comp (LinearMap.baseChange_surjective B' P.toKaehler_surjective)).comp
        e₀.toLinearEquiv.surjective)
      ((eH'.surjective.comp Q.toKaehler_surjective).comp e₀'.toLinearEquiv.surjective)
      (ModuleCat.ofHom (eH'.toLinearMap ∘ₗ
        (KaehlerDifferential.map A A' B B').liftBaseChange B' ∘ₗ eH.symm.toLinearMap))
      (eH'.bijective.comp (h₀.comp eH.symm.bijective)) ?_
    change φ.f 0 ≫ q' = q ≫ _
    dsimp only [q, q']
    rw [hφ₀]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    apply congrArg (fun z => e₀.hom ≫ z)
    apply ModuleCat.hom_ext
    apply ((Generators.self A B).cotangentSpaceBasis.baseChange B').ext
    intro x
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      Module.Basis.baseChange_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, one_smul]
    apply congrArg eH'
    rw [Generators.cotangentSpaceBasis_apply]
    exact toKaehler_map_tmul_D P Q f 1 (MvPolynomial.X x)
  · rw [quasiIsoAt_iff' φ 2 1 0 (by simp) (by simp)]
    let i := ModuleCat.ofHom (P.h1Cotangentι.baseChange B') ≫ e₁.inv
    let i' := ModuleCat.ofHom Q.h1Cotangentι ≫ e₁'.inv
    refine quasiIso_of_kernel_map _
      (double_d_eq_zero₀ d hrel 2 1 (by omega))
      (double_d_eq_zero₀ d' hrel 2 1 (by omega)) i i'
      (exact_double_left (ModuleCat.ofHom (P.h1Cotangentι.baseChange B')) d
        (Module.Flat.lTensor_exact B' P.exact_hCotangentι_cotangentComplex))
      (exact_double_left (ModuleCat.ofHom Q.h1Cotangentι) d' Q.exact_hCotangentι_cotangentComplex)
      (e₁.symm.toLinearEquiv.injective.comp
        (Module.Flat.lTensor_preserves_injective_linearMap P.h1Cotangentι
          Extension.h1Cotangentι_injective))
      (e₁'.symm.toLinearEquiv.injective.comp Extension.h1Cotangentι_injective)
      (ModuleCat.ofHom ((H1Cotangent.map A A' B B').liftBaseChange B')) h₁ ?_
    change i ≫ φ.f 1 = _ ≫ i'
    dsimp only [i, i']
    rw [hφ₁]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, ← Category.assoc]
    apply congrArg (fun z => z ≫ e₁'.inv)
    apply ModuleCat.hom_ext
    apply AlgebraTensorModule.ext
    intro a x
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, map_smul]
    rfl
  · apply (quasiIsoAt_iff_exactAt φ (n + 2)
      (ShortComplex.exact_of_isZero_X₂ _ (isZero_double_X d hrel _ (by omega) (by omega)))).mpr
    exact ShortComplex.exact_of_isZero_X₂ _
      (isZero_double_X d' hrel _ (by omega) (by omega))

/-- For a commutative square of rings `A → B`, `A' → B'` in which both vertical maps are
filtered colimits of étale maps, the canonical comparison map `NL_{B/A} ⊗_B B' ⟶ NL_{B'/A'}`
induces isomorphisms on all homology groups.

This is the engine of Stacks 0D08: the source's proof uses of the two henselizations only that
they are filtered colimits of étale algebras over their bases, so the statement holds at that
generality. Local and strict henselization of a local ring are the instances the source states;
the henselization of a pair is another, and is the one Stacks 0DZC's proof needs. -/
public theorem quasiIso_baseChangeComparison_of_ind_etale
    (A A' : Type u) (B B' : Type v) [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A A'] [Algebra A B] [Algebra B B'] [Algebra A' B'] [Algebra A B']
    [IsScalarTower A B B'] [IsScalarTower A A' B']
    (hA : (CommAlgCat.etale.{u} A).ind.{u} (CommAlgCat.of A A'))
    (hB : (CommAlgCat.etale.{v} B).ind.{v} (CommAlgCat.of B B')) :
    QuasiIso (naiveCotangentComplexBaseChangeComparison A A' B B') := by
  have : FormallyEtale A A' := formallyEtale_of_ind_etale hA
  have : FormallyEtale B B' := formallyEtale_of_ind_etale hB
  have : Module.Flat B B' := CommAlgCat.flat_of_ind_etale hB
  exact quasiIso_baseChangeComparison_of_bijective A A' B B'
    (h1Cotangent_liftBaseChange_bijective_of_ind_etale_square A A' B B' hA hB)
    (kaehlerDifferential_liftBaseChange_bijective_of_formallyEtale A A' B B')

-- `_hphi` and `_hinduced` pin down the map `Aˢʰ → Bˢʰ` that the statement speaks about, so they
-- belong to it even though the proof reads the ind-étale conditions off the instances alone.
/-- Let `A → B` be a local homomorphism of local rings. For the induced local map between
henselizations and the induced local map between strict henselizations associated to a compatible
map of residue fields, the canonical maps
`NL_{B/A} ⊗_B Bʰ ⟶ NL_{Bʰ/Aʰ}` and `NL_{B/A} ⊗_B Bˢʰ ⟶ NL_{Bˢʰ/Aˢʰ}` induce
isomorphisms on all homology groups. -/
@[stacks 0D08]
public theorem
    naiveCotangentComplex_quasiIso_henselization_and_strictHenselization
    (A Ah Ash : Type u) (B Bh Bsh : Type v) (kAsep : Type u) (kBsep : Type v)
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsLocalRing.IsHenselization A (IsLocalRing.ResidueField A) Ah]
    [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh]
    [IsLocalRing.IsHenselization B (IsLocalRing.ResidueField B) Bh]
    [Algebra A Bh] [IsScalarTower A B Bh] [Algebra Ah Bh] [IsScalarTower A Ah Bh]
    [IsLocalHom (algebraMap Ah Bh)]
    [Field kAsep] [Algebra (IsLocalRing.ResidueField A) kAsep]
    [IsSepClosure (IsLocalRing.ResidueField A) kAsep]
    [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]
    [IsLocalRing.IsHenselization A kAsep Ash]
    [Field kBsep] [Algebra (IsLocalRing.ResidueField B) kBsep]
    [IsSepClosure (IsLocalRing.ResidueField B) kBsep]
    [CommRing Bsh] [IsLocalRing Bsh] [Algebra B Bsh]
    [IsLocalRing.IsHenselization B kBsep Bsh]
    [Algebra A Bsh] [IsScalarTower A B Bsh] [Algebra Ash Bsh] [IsScalarTower A Ash Bsh]
    [IsLocalHom (algebraMap Ash Bsh)]
    (phi : IsLocalRing.ResidueField Ash →+* IsLocalRing.ResidueField Bsh)
    (_hphi : phi.comp ((IsLocalRing.residue Ash).comp (algebraMap A Ash)) =
      (IsLocalRing.residue Bsh).comp (algebraMap A Bsh))
    (_hinduced : (IsLocalRing.residue Bsh).comp (algebraMap Ash Bsh) =
      phi.comp (IsLocalRing.residue Ash)) :
    QuasiIso (Algebra.naiveCotangentComplexBaseChangeComparison A Ah B Bh) ∧
      QuasiIso (Algebra.naiveCotangentComplexBaseChangeComparison A Ash B Bsh) :=
  ⟨quasiIso_baseChangeComparison_of_ind_etale A Ah B Bh
    (IsLocalRing.IsHenselization.ind_etale_of_universe_le (IsLocalRing.ResidueField A))
    (IsLocalRing.IsHenselization.ind_etale_of_universe_le (IsLocalRing.ResidueField B)),
  quasiIso_baseChangeComparison_of_ind_etale A Ash B Bsh
    (IsLocalRing.IsHenselization.ind_etale_of_universe_le kAsep)
    (IsLocalRing.IsHenselization.ind_etale_of_universe_le kBsep)⟩

/-! ### The henselization of a pair -/

/-- Over a fixed base `k`, the canonical comparison map `NL_{P/k} ⊗_P Pʰ ⟶ NL_{Pʰ/k}` induces
isomorphisms on all homology groups whenever `P → Pʰ` is a filtered colimit of étale maps.

This is the case `A = A' = k` of `quasiIso_baseChangeComparison_of_ind_etale`: the base is not
moved, and `k` is trivially a filtered colimit of étale `k`-algebras because it is étale over
itself. -/
public theorem quasiIso_baseChangeComparison_of_ind_etale_of_constant_base
    (k : Type u) [CommRing k] (P P' : Type v) [CommRing P] [CommRing P']
    [Algebra k P] [Algebra P P'] [Algebra k P'] [IsScalarTower k P P']
    (hP : (CommAlgCat.etale.{v} P).ind.{v} (CommAlgCat.of P P')) :
    QuasiIso (naiveCotangentComplexBaseChangeComparison k k P P') :=
  quasiIso_baseChangeComparison_of_ind_etale k k P P'
    (ObjectProperty.le_ind (CommAlgCat.etale.{u} k) _ (inferInstance : Algebra.Etale k k)) hP

/-- **Stacks 0D08 for the henselization of a pair.** Let `P` be an algebra over a commutative
ring `k`, let `J ⊆ P` be an ideal and let `(Pʰ, Jʰ)` be the henselization of the pair `(P, J)`,
described by the henselian-pair condition on `Pʰ` together with its universal property. Then the
canonical comparison map

`NL_{P/k} ⊗_P Pʰ ⟶ NL_{Pʰ/k}`

induces isomorphisms on all homology groups.

The source states Stacks 0D08 for the henselization and the strict henselization of a local
ring, which is
`naiveCotangentComplex_quasiIso_henselization_and_strictHenselization`. Its proof uses of those
two only that they are filtered colimits of étale algebras over their bases, and the
henselization of a pair is such a colimit by `ind_henselization`; this is the instance Stacks
0DZC's proof appeals to 0D08 for. -/
@[stacks 0D08 "the henselization-of-pairs case, which Stacks 0DZC's proof cites 0D08 for \
although 0D08's own statement is about the local and strict henselizations of a local ring: the \
input to the source's proof is that both vertical maps are filtered colimits of étale maps, \
which `ind_henselization` supplies for the henselization of a pair"]
public theorem naiveCotangentComplex_quasiIso_henselizationPair
    (k : Type u) [CommRing k] (P : Type v) [CommRing P] [Algebra k P] (J : Ideal P)
    (Ph : Type v) [CommRing Ph] [Algebra P Ph] [Algebra k Ph] [IsScalarTower k P Ph]
    (hhens : HenselianPair Ph (J.map (algebraMap P Ph)))
    (huniv : ∀ (C : Type v) (_ : CommRing C) (JC : Ideal C), HenselianPair C JC →
      ∀ f : P →+* C, J ≤ JC.comap f →
        ∃! g : Ph →+* C, g.comp (algebraMap P Ph) = f ∧
          J.map (algebraMap P Ph) ≤ JC.comap g) :
    QuasiIso (naiveCotangentComplexBaseChangeComparison k k P Ph) := by
  obtain ⟨e⟩ := nonempty_algEquiv_henselization P J Ph hhens huniv
  exact quasiIso_baseChangeComparison_of_ind_etale_of_constant_base k P Ph
    (((CommAlgCat.etale.{v} P).ind.{v}).prop_of_iso (CommAlgCat.isoMk e)
      (ind_henselization P J))

end Algebra

end
