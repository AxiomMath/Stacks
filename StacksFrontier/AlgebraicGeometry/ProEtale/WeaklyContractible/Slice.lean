module

public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.TestingFamily
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable

/-!
# Weak contractibility passes to a slice site

Let `J` be a Grothendieck topology on `C` and let `U` be an object of `C`. If `V ⟶ U` has
weakly contractible source, then it is a weakly contractible object of the slice site
`C/U`: sheaves on `C/U` are the sheaves on `C` over the sheafification of `U`, by Stacks
00Y1, and under that equivalence a locally surjective morphism over `U` comes from a locally
surjective morphism on `C`, where weak contractibility of `V` applies. Consequently a testing
family on `C` pulls back to a testing family on every slice site.

## Main definitions

* `Stacks.WeaklyContractible.testingFamily_over`: the testing family on `C/U` induced by one
  on `C`.

## Main results

* `Stacks.WeaklyContractible.weaklyContractible_over`: an arrow with weakly contractible source
  is a weakly contractible object of the slice site.
* `Stacks.WeaklyContractible.smallOverOfSmall`: the slice of a small site is small.
* `Stacks.WeaklyContractible.wEqualsLocallyBijective_types`: on a small site the weak
  equivalences of presheaves of types are the locally bijective morphisms.

## Implementation notes

`smallOverOfSmall` and `wEqualsLocallyBijective_types` are the two side conditions the slice
construction needs; both are declared `local instance` here, since the slice site inherits them
from the site but Lean has no way to find them from the ambient hypotheses. They are what
discharges, for a small site, the sheafification hypothesis `weaklyContractible_over` takes on
the slice; that hypothesis is an instance argument rather than a consequence of smallness, so
that an essentially small site — a chosen big pro-étale site, for instance — can supply it too.

## References

* [Stacks Project, Tag 0945](https://stacks.math.columbia.edu/tag/0945)
* [Stacks Project, Tag 00Y1](https://stacks.math.columbia.edu/tag/00Y1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.WeaklyContractible

/-- The slice of a small category over an object is small. -/
theorem smallOverOfSmall {C : Type u} [Category.{v} C] [Small.{v} C] (U : C) :
    Small.{v} (Over U) := by
  let : Small.{v} (Σ V : C, V ⟶ U) := small_sigma (fun V : C => V ⟶ U)
  apply small_of_surjective (f := fun x : Σ V : C, V ⟶ U => Over.mk x.2)
  intro Y
  obtain ⟨V, f, rfl⟩ := Y.mk_surjective
  exact ⟨⟨V, f⟩, rfl⟩

attribute [local instance] smallOverOfSmall

/-- On a small site the weak equivalences of presheaves of types are exactly the locally
bijective morphisms. -/
theorem wEqualsLocallyBijective_types
    {C : Type u} [Category.{v} C] [Small.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type v)] :
    J.WEqualsLocallyBijective (Type v) :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, v, u, v + 1, v, v, v} J

attribute [local instance] wEqualsLocallyBijective_types

/-- An arrow `f : V ⟶ U` whose source is weakly contractible is a weakly contractible object of
the slice site `C/U`. -/
theorem weaklyContractible_over
    {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {V U : C} [HasSheafify J (Type v)]
    [J.WEqualsLocallyBijective (Type v)] [HasSheafify (J.over U) (Type v)]
    (f : V ⟶ U) (hV : J.IsWeaklyContractible V) :
    (J.over U).IsWeaklyContractible (Over.mk f) := by
  let Φ := OverShriek.sheafFunctorToOver (U := U) J
  let Ψ := OverShriek.sheafFiberFunctor (U := U) J
  let : Φ.Full := OverShriek.full_sheafFunctorToOver (U := U) J
  let : Φ.Faithful := OverShriek.faithful_sheafFunctorToOver (U := U) J
  let : Φ.EssSurj := OverShriek.essSurj_sheafFunctorToOver (U := U) J
  let : Φ.IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  intro F G φ hφ s
  let : Epi φ := Sheaf.epi_of_isLocallySurjective φ
  let α := Φ.map φ
  have hαlocal : Sheaf.IsLocallySurjective α.left :=
    (Sheaf.isLocallySurjective_iff_epi α.left).2 ((Over.epi_iff_epi_left α).mp inferInstance)
  let η := OverShriek.sheafUnitIso (U := U) J
  let s' := (η.hom.app G).hom.app (op (Over.mk f)) s
  obtain ⟨x, hx⟩ := hV (Φ.obj F).left (Φ.obj G).left α.left hαlocal s'.1
  have hcomp : (Φ.obj G).hom.hom.app (op V) ((α.left).hom.app (op V) x) =
      (Φ.obj F).hom.hom.app (op V) x :=
    congrArg (fun ψ => ψ.hom.app (op V) x) α.w
  let x' : (Ψ.obj (Φ.obj F)).obj.obj (op (Over.mk f)) := by
    change {x : (Φ.obj F).left.obj.obj (op V) // _}
    refine ⟨x, ?_⟩
    change (Φ.obj F).hom.hom.app (op V) x = _
    have hx0 : (α.left).hom.app (op V) x = s'.1 := by simpa using hx
    rw [← hcomp, hx0]
    exact s'.2
  have hx' : ((Ψ.map α).hom.app (op (Over.mk f))) x' = s' := Subtype.ext hx
  let t' := (η.app F).inv.hom.app (op (Over.mk f)) x'
  have ht : φ.hom.app (op (Over.mk f)) t' = s := by
    have hinj : Function.Injective ((η.app G).hom.hom.app (op (Over.mk f))) :=
      ((isIso_iff_bijective _).mp inferInstance).1
    apply hinj
    calc
      (η.app G).hom.hom.app (op (Over.mk f)) (φ.hom.app (op (Over.mk f)) t') =
          ((Ψ.map α).hom.app (op (Over.mk f)))
            ((η.app F).hom.hom.app (op (Over.mk f)) t') := by
        simpa [Functor.comp_map, α, t'] using
        (congrArg (fun k => k.hom.app (op (Over.mk f)) t')
          (η.hom.naturality φ))
      _ = ((Ψ.map α).hom.app (op (Over.mk f))) x' := by
        congr 1
        exact congrArg (fun k => k.hom.app (op (Over.mk f)) x')
          (η.app F).inv_hom_id
      _ = s' := hx'
      _ = (η.hom.app G).hom.app (op (Over.mk f)) s := rfl
  exact ⟨t', ht⟩

/-- A weakly contractible testing family on a site induces one on every slice site: the arrows
whose source belongs to the family. -/
def testingFamily_over
    {C : Type u} [Category.{v} C] [Small.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J (Type v)]
    (h : WeaklyContractibleTestingFamily C J)
    (U : C) [HasSheafify (J.over U) (Type v)] :
    WeaklyContractibleTestingFamily (Over U) (J.over U) where
  B := fun W => h.B W.left
  isWeaklyContractible := by
    intro W hW
    exact weaklyContractible_over J W.hom (h.isWeaklyContractible hW)
  hasEnoughObjects := by
    intro W
    obtain ⟨I, V, f, hf, hV⟩ := h.hasEnoughObjects W.left
    let V' : I → Over U := fun i => Over.mk (f i ≫ W.hom)
    let g : (i : I) → V' i ⟶ W := fun i => Over.homMk (f i)
    have heq : Sieve.ofArrows V' g = (Sieve.overEquiv W).symm (Sieve.ofArrows V f) := by
      apply Sieve.ext
      intro Z q
      rw [Sieve.overEquiv_symm_iff, Sieve.mem_ofArrows_iff, Sieve.mem_ofArrows_iff]
      constructor
      · rintro ⟨i, a, rfl⟩
        exact ⟨i, a.left, rfl⟩
      · rintro ⟨i, a, ha⟩
        have hbase : a ≫ (f i ≫ W.hom) = Z.hom := by
          calc
            a ≫ (f i ≫ W.hom) = (a ≫ f i) ≫ W.hom := by
              rw [Category.assoc]
            _ = q.left ≫ W.hom := by rw [ha]
            _ = Z.hom := q.w
        exact ⟨i, Over.homMk a hbase, Over.OverMorphism.ext ha⟩
    refine ⟨I, V', g, ?_, hV⟩
    rw [heq]
    exact J.overEquiv_symm_mem_over W _ hf

end Stacks.WeaklyContractible

end
