module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantAbelian.ConstantSectionQuotient
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantAbelian.OverMapRestriction
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Morphisms
public import StacksFrontier.CategoryTheory.Sites.Localization.OverMapKanExtension
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms of locally constant sheaves of abelian groups

Let `J` be a Grothendieck topology on `C`. A map `φ : F ⟶ G` of locally constant abelian sheaves
whose source is *finite* locally constant is, locally on the site, induced by a homomorphism of
abelian groups: over every object `U` there is a covering `{X i ⟶ U}` and, on each member, local
trivializations `F|_{X i} ≅ A̲` and `G|_{X i} ≅ B̲` together with a homomorphism `g : A ⟶ B` whose
associated map of constant abelian sheaves is `φ|_{X i}`.

## Main definitions

* `Stacks.ConstantSheaf.IsConstantAbelianMapAt`: over an object `V`, the restriction of `φ` is the
  map of constant abelian sheaves associated to a homomorphism with finite source.
* `Stacks.ConstantSheaf.constantAbelianMapRestrict`: the restriction along `Over.map t` of a map of
  constant abelian sheaves, as a map of constant abelian sheaves.
* `Stacks.ConstantSheaf.overPullbackIsoOfMapAbelian`: a trivialization of a sheaf over `U` with
  value `E` gives a trivialization with value `E` over any `V` lying over `U`.

## Main results

* `Stacks.ConstantSheaf.exists_cover_isConstantAbelianMapAt`: given trivializations of `F` and `G`
  over one object, with finite value for `F`, the restriction of `φ` is induced by a homomorphism
  of abelian groups on a covering of that object.
* `Stacks.ConstantSheaf.exists_cover_restrict_eq_constantSheaf_map_abelian`: a map of locally
  constant abelian sheaves with finite locally constant source is, on a covering of any object,
  induced by a homomorphism of abelian groups.
* `Stacks.ConstantSheaf.exists_cover_restrict_eq_constantSheaf_map_abelian_smallSite`: the same on
  a small site, with the abelian groups in the universe of the site.

## References

* [Stacks Project, Tag 093S](https://stacks.math.columbia.edu/tag/093S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.ConstantSheaf

/-- Values on a generating family of an abelian group which respect every relation of that family
descend to a homomorphism. -/
lemma exists_hom_of_generatorImages {A B : Ab.{w}} (n : ℕ) (z : Fin n → A)
    (hz : Function.Surjective (Finsupp.linearCombination ℤ z)) (b : Fin n → B)
    (hrel : ∀ x : Fin n →₀ ℤ, Finsupp.linearCombination ℤ z x = 0 →
      Finsupp.linearCombination ℤ b x = 0) :
    ∃ g : A ⟶ B, ∀ i, g (z i) = b i := by
  let p := Finsupp.linearCombination ℤ z
  let q := Finsupp.linearCombination ℤ b
  have hpq : LinearMap.ker p ≤ LinearMap.ker q := fun x hx => hrel x (LinearMap.mem_ker.mp hx)
  let ε := p.quotKerEquivOfSurjective hz
  refine ⟨AddCommGrpCat.ofHom
    (((LinearMap.ker p).liftQ q hpq).comp ε.symm.toLinearMap).toAddMonoidHom, fun i => ?_⟩
  have heq : ε.symm (z i) = Submodule.Quotient.mk (Finsupp.single i (1 : ℤ)) := by
    apply ε.injective
    simp [ε, p, Finsupp.linearCombination_single]
  show ((LinearMap.ker p).liftQ q hpq) (ε.symm (z i)) = b i
  rw [heq]
  calc ((LinearMap.ker p).liftQ q hpq) (Submodule.Quotient.mk (Finsupp.single i (1 : ℤ)))
      = q (Finsupp.single i 1) := DFunLike.congr_fun (Submodule.liftQ_mkQ (LinearMap.ker p) q hpq) _
    _ = b i := by simp [q, Finsupp.linearCombination_single]

/-- Values on a generating family which an injective homomorphism makes compatible with the
generators descend to a homomorphism. -/
lemma exists_hom_of_generatorImages_of_injective {A B D : Ab.{w}} (n : ℕ) (z : Fin n → A)
    (hz : Function.Surjective (Finsupp.linearCombination ℤ z)) (b : Fin n → B)
    (f : A ⟶ D) (g : B ⟶ D) (hg : Function.Injective g) (h : ∀ j, g (b j) = f (z j)) :
    ∃ gh : A ⟶ B, ∀ i, gh (z i) = b i := by
  refine exists_hom_of_generatorImages n z hz b fun x hx => hg ?_
  rw [map_zero]
  calc g (Finsupp.linearCombination ℤ b x)
      = Finsupp.linearCombination ℤ (fun j => g (b j)) x :=
        Finsupp.apply_linearCombination ℤ g.hom.toIntLinearMap b x
    _ = Finsupp.linearCombination ℤ (fun j => f (z j)) x := by simp only [h]
    _ = f (Finsupp.linearCombination ℤ z x) :=
        (Finsupp.apply_linearCombination ℤ f.hom.toIntLinearMap z x).symm
    _ = 0 := by rw [hx, map_zero]

/-- A finite abelian group is generated, as a `ℤ`-module, by an enumeration of its elements. -/
lemma exists_fin_generators_of_finite (A : Ab.{w}) [Finite A] :
    ∃ (n : ℕ) (z : Fin n → A), Function.Surjective (Finsupp.linearCombination ℤ z) := by
  classical
  have := Fintype.ofFinite (A : Type w)
  refine ⟨Fintype.card (A : Type w), (Fintype.equivFin (A : Type w)).symm, fun a => ?_⟩
  refine ⟨Finsupp.single (Fintype.equivFin (A : Type w) a) 1, ?_⟩
  simp

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) [HasWeakSheafify K Ab.{w}]

/-- Two maps out of a constant abelian sheaf which agree on the constant sections of a generating
family, over a final object, are equal. -/
lemma constantSheaf_hom_ext_of_generators {T : C} (hT : IsTerminal T) (A : Ab.{w})
    (Q : Sheaf K Ab.{w}) (n : ℕ) (z : Fin n → A)
    (hz : Function.Surjective (Finsupp.linearCombination ℤ z))
    (a b : (constantSheaf K Ab.{w}).obj A ⟶ Q)
    (h : ∀ i, a.hom.app (op T)
        ((CategoryTheory.toSheafify K ((Functor.const Cᵒᵖ).obj A)).app (op T) (z i)) =
      b.hom.app (op T)
        ((CategoryTheory.toSheafify K ((Functor.const Cᵒᵖ).obj A)).app (op T) (z i))) :
    a = b := by
  let η := CategoryTheory.toSheafify K ((Functor.const Cᵒᵖ).obj A)
  let a' := η ≫ a.hom
  let b' := η ≫ b.hom
  have he : a'.app (op T) = b'.app (op T) := by
    have hc : (a'.app (op T)).hom.toIntLinearMap.comp (Finsupp.linearCombination ℤ z) =
        (b'.app (op T)).hom.toIntLinearMap.comp (Finsupp.linearCombination ℤ z) := by
      ext i
      show a'.app (op T) (Finsupp.linearCombination ℤ z (Finsupp.single i 1)) =
        b'.app (op T) (Finsupp.linearCombination ℤ z (Finsupp.single i 1))
      rw [Finsupp.linearCombination_single, one_smul]
      exact h i
    ext x
    obtain ⟨y, rfl⟩ := hz x
    exact DFunLike.congr_fun hc y
  refine Sheaf.hom_ext (sheafify_hom_ext K _ _ Q.property (NatTrans.ext (funext fun V => ?_)))
  have ha := a'.naturality (hT.from V.unop).op
  rw [he] at ha
  simpa using ha.trans (b'.naturality (hT.from V.unop).op).symm

end Stacks.ConstantSheaf

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [∀ U : C, HasWeakSheafify (J.over U) Ab.{w}]

/-- Over the object `V`, the restriction of `φ` is the map of constant abelian sheaves associated
to a homomorphism of abelian groups with finite source. -/
abbrev IsConstantAbelianMapAt (F G : Sheaf J Ab.{w}) (φ : F ⟶ G) (V : C) : Prop :=
  ∃ (A B : Ab.{w}), Finite (A : Type w) ∧
    ∃ (g : A ⟶ B)
      (eF : (constantSheaf (J.over V) Ab.{w}).obj A ≅ (J.overPullback Ab.{w} V).obj F)
      (eG : (constantSheaf (J.over V) Ab.{w}).obj B ≅ (J.overPullback Ab.{w} V).obj G),
      (constantSheaf (J.over V) Ab.{w}).map g ≫ eG.hom =
        eF.hom ≫ (J.overPullback Ab.{w} V).map φ

/-- The object of `Over U` over which the constant sections of `Over V` are read. -/
lemma overMap_op_obj_mkId {U V : C} (t : V ⟶ U) :
    (Over.map t).op.obj (op (Over.mk (𝟙 V))) = op (Over.mk t) := by
  show op (Over.mk (𝟙 V ≫ t)) = _
  rw [Category.id_comp]

section OverMap

variable [UnivLE.{max u v, w}] {U V : C} (t : V ⟶ U)

/-- The restriction along `Over.map t` of a map of constant abelian sheaves on `Over U`, read as a
map of constant abelian sheaves on `Over V`. -/
def constantAbelianMapRestrict (A B : Ab.{w})
    (ψ : (constantSheaf (J.over U) Ab.{w}).obj A ⟶ (constantSheaf (J.over U) Ab.{w}).obj B) :
    (constantSheaf (J.over V) Ab.{w}).obj A ⟶ (constantSheaf (J.over V) Ab.{w}).obj B :=
  (constantSheafOverMapIso J Ab.{w} t A).hom ≫ (J.overMapPullback Ab.{w} t).map ψ ≫
    (constantSheafOverMapIso J Ab.{w} t B).inv

/-- **A trivialization survives refinement.** If a sheaf of abelian groups becomes constant with
value `E` after restriction to `U`, it becomes constant with the *same* value `E` after restriction
to any `V` lying over `U`. -/
def overPullbackIsoOfMapAbelian (F : Sheaf J Ab.{w}) (E : Ab.{w})
    (e : (constantSheaf (J.over U) Ab.{w}).obj E ≅ (J.overPullback Ab.{w} U).obj F) :
    (constantSheaf (J.over V) Ab.{w}).obj E ≅ (J.overPullback Ab.{w} V).obj F :=
  constantSheafOverMapIso J Ab.{w} t E ≪≫ (J.overMapPullback Ab.{w} t).mapIso e

/-- The forward map of `Stacks.ConstantSheaf.overPullbackIsoOfMapAbelian`, unfolded. -/
lemma overPullbackIsoOfMapAbelian_hom (F : Sheaf J Ab.{w}) (E : Ab.{w})
    (e : (constantSheaf (J.over U) Ab.{w}).obj E ≅ (J.overPullback Ab.{w} U).obj F) :
    (overPullbackIsoOfMapAbelian J t F E e).hom =
      (constantSheafOverMapIso J Ab.{w} t E).hom ≫ (J.overMapPullback Ab.{w} t).map e.hom :=
  rfl

/-- The restricted map is compatible with the two restriction isomorphisms. -/
lemma constantAbelianMapRestrict_comp (A B : Ab.{w})
    (ψ : (constantSheaf (J.over U) Ab.{w}).obj A ⟶ (constantSheaf (J.over U) Ab.{w}).obj B) :
    constantAbelianMapRestrict J t A B ψ ≫ (constantSheafOverMapIso J Ab.{w} t B).hom =
      (constantSheafOverMapIso J Ab.{w} t A).hom ≫ (J.overMapPullback Ab.{w} t).map ψ := by
  dsimp only [constantAbelianMapRestrict]
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- A constant section of the restricted sheaf on `Over V` which, read on `Over U`, represents the
image of a constant section of `A̲` represents it already on `Over V`. -/
lemma constantAbelianMapRestrict_section (A B : Ab.{w})
    (ψ : (constantSheaf (J.over U) Ab.{w}).obj A ⟶ (constantSheaf (J.over U) Ab.{w}).obj B)
    (a : A) (b : B)
    (h : (CategoryTheory.toSheafify (J.over U)
          ((Functor.const (Over U)ᵒᵖ).obj B)).app (op (Over.mk t)) b =
      ψ.hom.app (op (Over.mk t)) ((CategoryTheory.toSheafify (J.over U)
        ((Functor.const (Over U)ᵒᵖ).obj A)).app (op (Over.mk t)) a)) :
    (CategoryTheory.toSheafify (J.over V)
        ((Functor.const (Over V)ᵒᵖ).obj B)).app (op (Over.mk (𝟙 V))) b =
      (constantAbelianMapRestrict J t A B ψ).hom.app (op (Over.mk (𝟙 V)))
        ((CategoryTheory.toSheafify (J.over V)
          ((Functor.const (Over V)ᵒᵖ).obj A)).app (op (Over.mk (𝟙 V))) a) := by
  set Ti : (Over V)ᵒᵖ := op (Over.mk (𝟙 V)) with hTi
  set oA := constantSheafOverMapIso J Ab.{w} t A with hoA
  set oB := constantSheafOverMapIso J Ab.{w} t B with hoB
  have hinj := (ConcreteCategory.bijective_of_isIso (oB.hom.hom.app Ti)).injective
  apply hinj
  have hA := ConcreteCategory.congr_hom
    (NatTrans.congr_app (constantSheafOverMapIso_unit J Ab.{w} t A) Ti) a
  have hB := ConcreteCategory.congr_hom
    (NatTrans.congr_app (constantSheafOverMapIso_unit J Ab.{w} t B) Ti) b
  have hcomp := ConcreteCategory.congr_hom
    (NatTrans.congr_app
      (Sheaf.hom_ext_iff.mp (constantAbelianMapRestrict_comp J t A B ψ)) Ti)
    ((CategoryTheory.toSheafify (J.over V) ((Functor.const (Over V)ᵒᵖ).obj A)).app Ti a)
  change oB.hom.hom.app Ti
      ((CategoryTheory.toSheafify (J.over V) ((Functor.const (Over V)ᵒᵖ).obj B)).app Ti b) =
    (CategoryTheory.toSheafify (J.over U)
      ((Functor.const (Over U)ᵒᵖ).obj B)).app ((Over.map t).op.obj Ti) b at hB
  change oA.hom.hom.app Ti
      ((CategoryTheory.toSheafify (J.over V) ((Functor.const (Over V)ᵒᵖ).obj A)).app Ti a) =
    (CategoryTheory.toSheafify (J.over U)
      ((Functor.const (Over U)ᵒᵖ).obj A)).app ((Over.map t).op.obj Ti) a at hA
  change oB.hom.hom.app Ti
      ((constantAbelianMapRestrict J t A B ψ).hom.app Ti
        ((CategoryTheory.toSheafify (J.over V)
          ((Functor.const (Over V)ᵒᵖ).obj A)).app Ti a)) =
    ψ.hom.app ((Over.map t).op.obj Ti) (oA.hom.hom.app Ti
      ((CategoryTheory.toSheafify (J.over V)
        ((Functor.const (Over V)ᵒᵖ).obj A)).app Ti a)) at hcomp
  rw [hB, hcomp, hA]
  let P (Z : (Over U)ᵒᵖ) : Prop :=
    (CategoryTheory.toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj B)).app Z b =
      ψ.hom.app Z ((CategoryTheory.toSheafify (J.over U)
        ((Functor.const (Over U)ᵒᵖ).obj A)).app Z a)
  exact (congrArg P (overMap_op_obj_mkId t)).mpr h

end OverMap

section Engine

variable [UnivLE.{max u v, w}]

/-- Given trivializations of `F` and of `G` over the same object `U`, the value of `F` being
finite, there is a covering of `U` on each member of which the restriction of `φ` is the map of
constant abelian sheaves associated to a homomorphism of abelian groups. -/
lemma exists_cover_isConstantAbelianMapAt (F G : Sheaf J Ab.{w}) (φ : F ⟶ G) (U : C)
    (A B : Ab.{w}) [Finite A]
    (eF : (constantSheaf (J.over U) Ab.{w}).obj A ≅ (J.overPullback Ab.{w} U).obj F)
    (eG : (constantSheaf (J.over U) Ab.{w}).obj B ≅ (J.overPullback Ab.{w} U).obj G) :
    ∃ (I : Type (max u v)) (X : I → C) (f : ∀ i, X i ⟶ U),
      Sieve.ofArrows X f ∈ J U ∧ ∀ i, IsConstantAbelianMapAt J F G φ (X i) := by
  classical
  obtain ⟨n, z, hz⟩ := exists_fin_generators_of_finite A
  set ψ : (constantSheaf (J.over U) Ab.{w}).obj A ⟶ (constantSheaf (J.over U) Ab.{w}).obj B :=
    eF.hom ≫ (J.overPullback Ab.{w} U).map φ ≫ eG.inv with hψdef
  have hψ : ψ ≫ eG.hom = eF.hom ≫ (J.overPullback Ab.{w} U).map φ := by
    rw [hψdef, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  set ηA := CategoryTheory.toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj A) with hηA
  set ηB := CategoryTheory.toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj B) with hηB
  set T : Over U := Over.mk (𝟙 U) with hTdef
  obtain ⟨I, W, k, hk, hm⟩ := Stacks.Sheafification.exists_cover_representatives (J.over U) ηB T
    (fun j => ψ.hom.app (op T) (ηA.app (op T) (z j)))
  refine ⟨I, fun i => (W i).left, fun i => (W i).hom, ?_, fun i => ?_⟩
  · rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows] at hk
    change Sieve.ofArrows (fun i => (W i).left) (fun i => (k i).left) ∈ J U at hk
    have hleft : (fun i => (W i).hom) = fun i => (k i).left := by
      funext i
      exact ((Category.comp_id ((k i).left)).symm.trans (Over.w (k i))).symm
    rw [hleft]
    exact hk
  · obtain ⟨-, hrep⟩ := hm i
    choose b hb using hrep
    set t : (W i).left ⟶ U := (W i).hom with htdef
    have hTiTerm : IsTerminal (Over.mk (𝟙 (W i).left)) := Over.mkIdTerminal
    set Bq := constantQuotient (J.over (W i).left) (Over.mk (𝟙 (W i).left)) B with hBq
    set pr : B ⟶ Bq := constantQuotientMk (J.over (W i).left)
      (Over.mk (𝟙 (W i).left)) B with hpr
    have hprIso := isIso_constantSheaf_map_constantQuotientMk (J.over (W i).left) hTiTerm B
    set ηAi := CategoryTheory.toSheafify (J.over (W i).left)
      ((Functor.const (Over (W i).left)ᵒᵖ).obj A) with hηAi
    set ηBi := CategoryTheory.toSheafify (J.over (W i).left)
      ((Functor.const (Over (W i).left)ᵒᵖ).obj B) with hηBi
    set ηBqi := CategoryTheory.toSheafify (J.over (W i).left)
      ((Functor.const (Over (W i).left)ᵒᵖ).obj Bq) with hηBqi
    set cpr := (constantSheaf (J.over (W i).left) Ab.{w}).map pr with hcpr
    have hpt : ∀ j, ηB.app (op (Over.mk t)) (b j) =
        ψ.hom.app (op (Over.mk t)) (ηA.app (op (Over.mk t)) (z j)) := by
      intro j
      have h1 := ConcreteCategory.congr_hom (ηA.naturality (k i).op) (z j)
      have h2 := ConcreteCategory.congr_hom (ψ.hom.naturality (k i).op)
        (ηA.app (op T) (z j))
      change ηA.app (op (W i)) (z j) =
        ((constantSheaf (J.over U) Ab.{w}).obj A).obj.map (k i).op (ηA.app (op T) (z j)) at h1
      change ψ.hom.app (op (W i))
          (((constantSheaf (J.over U) Ab.{w}).obj A).obj.map (k i).op
            (ηA.app (op T) (z j))) =
        ((constantSheaf (J.over U) Ab.{w}).obj B).obj.map (k i).op
          (ψ.hom.app (op T) (ηA.app (op T) (z j))) at h2
      show ηB.app (op (W i)) (b j) = ψ.hom.app (op (W i)) (ηA.app (op (W i)) (z j))
      rw [h1, h2]
      exact (hb j).symm
    have hsec : ∀ j, ηBi.app (op (Over.mk (𝟙 (W i).left))) (b j) =
        (constantAbelianMapRestrict J t A B ψ).hom.app (op (Over.mk (𝟙 (W i).left)))
          (ηAi.app (op (Over.mk (𝟙 (W i).left))) (z j)) := fun j =>
      constantAbelianMapRestrict_section J t A B ψ (z j) (b j) (hpt j)
    have hnat : ∀ {X Y : Ab.{w}} (f : X ⟶ Y) (y : X),
        (CategoryTheory.toSheafify (J.over (W i).left)
          ((Functor.const (Over (W i).left)ᵒᵖ).obj Y)).app (op (Over.mk (𝟙 (W i).left))) (f y) =
        ((constantSheaf (J.over (W i).left) Ab.{w}).map f).hom.app
          (op (Over.mk (𝟙 (W i).left)))
          ((CategoryTheory.toSheafify (J.over (W i).left)
            ((Functor.const (Over (W i).left)ᵒᵖ).obj X)).app (op (Over.mk (𝟙 (W i).left))) y) :=
      fun f y => ConcreteCategory.congr_hom (NatTrans.congr_app
        (CategoryTheory.toSheafify_naturality (J.over (W i).left)
          ((Functor.const (Over (W i).left)ᵒᵖ).map f)) (op (Over.mk (𝟙 (W i).left)))) y
    have hfz : ∀ j, (ηBqi.app (op (Over.mk (𝟙 (W i).left)))) (pr (b j)) =
        (ηAi.app (op (Over.mk (𝟙 (W i).left))) ≫
          (constantAbelianMapRestrict J t A B ψ).hom.app (op (Over.mk (𝟙 (W i).left))) ≫
          cpr.hom.app (op (Over.mk (𝟙 (W i).left)))) (z j) := by
      intro j
      rw [hnat pr (b j), hsec j]
      rfl
    obtain ⟨gh, hgh⟩ := exists_hom_of_generatorImages_of_injective n z hz (fun j => pr (b j))
      (ηAi.app (op (Over.mk (𝟙 (W i).left))) ≫
        (constantAbelianMapRestrict J t A B ψ).hom.app (op (Over.mk (𝟙 (W i).left))) ≫
        cpr.hom.app (op (Over.mk (𝟙 (W i).left))))
      (ηBqi.app (op (Over.mk (𝟙 (W i).left))))
      (injective_constantSection_constantQuotient (J.over (W i).left) hTiTerm B) hfz
    have hstep : (constantSheaf (J.over (W i).left) Ab.{w}).map gh =
        constantAbelianMapRestrict J t A B ψ ≫ cpr := by
      refine constantSheaf_hom_ext_of_generators (J.over (W i).left) hTiTerm A _ n z hz _ _
        fun j => ?_
      rw [← hnat gh (z j), hgh j, hnat pr (b j), hsec j]
      rfl
    have hsq : constantAbelianMapRestrict J t A B ψ ≫
          (overPullbackIsoOfMapAbelian J t G B eG).hom =
        (overPullbackIsoOfMapAbelian J t F A eF).hom ≫
          (J.overPullback Ab.{w} (W i).left).map φ := by
      show constantAbelianMapRestrict J t A B ψ ≫ (constantSheafOverMapIso J Ab.{w} t B).hom ≫
          (J.overMapPullback Ab.{w} t).map eG.hom =
        ((constantSheafOverMapIso J Ab.{w} t A).hom ≫
            (J.overMapPullback Ab.{w} t).map eF.hom) ≫
          (J.overMapPullback Ab.{w} t).map ((J.overPullback Ab.{w} U).map φ)
      rw [← Category.assoc, constantAbelianMapRestrict_comp J t A B ψ, Category.assoc,
        ← CategoryTheory.Functor.map_comp, hψ, CategoryTheory.Functor.map_comp, Category.assoc]
    refine ⟨A, Bq, inferInstance, gh, overPullbackIsoOfMapAbelian J t F A eF,
      (asIso cpr).symm ≪≫ overPullbackIsoOfMapAbelian J t G B eG, ?_⟩
    rw [hstep]
    simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.hom_inv_id_assoc]
    exact hsq

/-- A morphism of locally constant sheaves of abelian groups whose source is finite locally
constant is, on a covering of any object, obtained from a homomorphism of abelian groups. -/
@[stacks 093S "part (2), sheaves of abelian groups; assumes pointwise right Kan extensions along \
  the localization functors, a limit-existence side condition implied by fibre products in the \
  site", sga "4 IX 2.1" "(ii) map, abelian"]
lemma exists_cover_restrict_eq_constantSheaf_map_abelian
    (F G : Sheaf J Ab.{w}) (φ : F ⟶ G)
    [hF : IsFiniteLocallyConstant J F] [hG : IsLocallyConstant J G] (U : C) :
    ∃ (I : Type (max u v)) (X : I → C) (f : ∀ i, X i ⟶ U),
      Sieve.ofArrows X f ∈ J U ∧ ∀ i,
        ∃ (A B : Ab.{w}), Finite (A : Type w) ∧
          ∃ (g : A ⟶ B)
            (eF : (constantSheaf (J.over (X i)) Ab.{w}).obj A ≅
              (J.overPullback Ab.{w} (X i)).obj F)
            (eG : (constantSheaf (J.over (X i)) Ab.{w}).obj B ≅
              (J.overPullback Ab.{w} (X i)).obj G),
              (constantSheaf (J.over (X i)) Ab.{w}).map g ≫ eG.hom =
                eF.hom ≫ (J.overPullback Ab.{w} (X i)).map φ := by
  classical
  obtain ⟨I, Y, f, hf, hGc⟩ := hG.exists_cover U
  apply exists_cover_trans J (P := IsConstantAbelianMapAt J F G φ) hf
  intro i
  obtain ⟨B, ⟨eB⟩⟩ := (hGc i).mem_essImage
  obtain ⟨I', Z, g, hg, hFc⟩ := hF.exists_finite_cover (Y i)
  apply exists_cover_trans J (P := IsConstantAbelianMapAt J F G φ) hg
  intro j
  obtain ⟨A, hA, ⟨eA⟩⟩ := hFc j
  have : Finite (A : Type w) := hA
  exact exists_cover_isConstantAbelianMapAt J F G φ (Z j) A B eA
    (overPullbackIsoOfMapAbelian J (g j) G B eB)

end Engine

section SmallSite

/-- On a small site `C : Type u`, with the abelian groups in the universe `u`, a morphism of
locally constant sheaves of abelian groups whose source is finite locally constant is, on a
covering of any object, obtained from a homomorphism of abelian groups. -/
@[stacks 093S "part (2), sheaves of abelian groups", sga "4 IX 2.1" "(ii) map, abelian"]
lemma exists_cover_restrict_eq_constantSheaf_map_abelian_smallSite
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (F G : Sheaf J Ab.{u}) (φ : F ⟶ G)
    [IsFiniteLocallyConstant J F] [IsLocallyConstant J G] (U : C) :
    ∃ (I : Type u) (X : I → C) (f : ∀ i, X i ⟶ U),
      Sieve.ofArrows X f ∈ J U ∧ ∀ i,
        ∃ (A B : Ab.{u}), Finite (A : Type u) ∧
          ∃ (g : A ⟶ B)
            (eF : (constantSheaf (J.over (X i)) Ab.{u}).obj A ≅
              (J.overPullback Ab.{u} (X i)).obj F)
            (eG : (constantSheaf (J.over (X i)) Ab.{u}).obj B ≅
              (J.overPullback Ab.{u} (X i)).obj G),
              (constantSheaf (J.over (X i)) Ab.{u}).map g ≫ eG.hom =
                eF.hom ≫ (J.overPullback Ab.{u} (X i)).map φ :=
  exists_cover_restrict_eq_constantSheaf_map_abelian J F G φ U

end SmallSite

end Stacks.ConstantSheaf

end
