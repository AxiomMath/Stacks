module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleToposCoherence

/-!
# The canonical isomorphism attached to a presentation, and its cocycle condition

Let `X` be an algebraic space over a scheme `S`, let `φ : U ⟶ X` be a surjective étale morphism
presenting `X` as `U/R`, and let `(U, R, s, t, c, e, i)` be the resulting groupoid, so that
`R = U ×_X U` with `t` and `s` the two projections and `c` the composition law on
`R ×_{s, U, t} R`.

For a sheaf `ℱ` on the small étale site of `X`, write `𝒢 = φ⁻¹ℱ` for its pullback to `U`.
Since `t ≫ φ = s ≫ φ`, the functoriality of the small étale pullback in the morphism supplies a
canonical isomorphism

`α : t⁻¹𝒢 ⟶ s⁻¹𝒢`,

and the same functoriality makes `α` satisfy the cocycle condition on `R ×_{s, U, t} R`: the two
ways of comparing `pr₀⁻¹t⁻¹𝒢` with `c⁻¹s⁻¹𝒢`, one through `pr₀⁻¹α` and `pr₁⁻¹α` and the other
through `c⁻¹α`, agree. All pullbacks are the *small* étale ones, that is the inverse images of
the morphisms of small étale topoi of Stacks 03G2, part (3), interpreted as in Stacks 03LP.

## Main definitions

* `CategoryTheory.compIsoOfEq`: for a family of pullback functors with composition comparison
  isomorphisms, the canonical identification of the two iterated pullbacks along two composable
  pairs of morphisms with the same composite, and `CategoryTheory.compIsoOfEqApp` the same read
  on a single object;
* `CategoryTheory.IsCompIsoCoherent`: the associativity coherence of a family of composition
  comparison isomorphisms;
* `AlgebraicGeometry.Space.inverseImageCompIsoOfEq` and
  `AlgebraicGeometry.Space.inverseImageCompIsoOfEqApp`: the same identification for the small
  étale inverse images;
* `AlgebraicGeometry.Space.presentationPullbackIso` and
  `AlgebraicGeometry.Space.presentationPullbackIsoApp`: the isomorphism `α` of Stacks 05YY, as a
  natural isomorphism in `ℱ` and read on the sheaf `𝒢 = φ⁻¹ℱ`.

## Main results

* `CategoryTheory.compIsoOfEqApp_cocycle`: the cocycle condition for a family of pullback
  functors whose composition comparison isomorphisms satisfy the associativity coherence;
* `AlgebraicGeometry.Space.presentationPullbackIsoApp_cocycle`: the cocycle condition on
  `R ×_{s, U, t} R` satisfied by `α`, that is the commutativity of the pentagon of Stacks 05YY.

## Implementation notes

Every edge of the pentagon, and `α` itself, is an instance of one construction: two composable
pairs of morphisms with the same composite have canonically identified iterated pullbacks, which
is `CategoryTheory.compIsoOfEq`. The three edges of the pentagon drawn as equalities in the
source are the instances in which the second morphism of each pair is `s` or `t`, and `α` is the
instance in which it is `φ` twice.

The cocycle condition is proved by straightening each of the six corners against the pullback
along a single morphism `R ×_{s, U, t} R ⟶ X`: for `m : R ×_{s, U, t} R ⟶ R` and `n : R ⟶ U`, the
iterated pullback of `𝒢` along `n` and then `m` is compared with the pullback of `ℱ` along
`(m ≫ n) ≫ φ`. Against those comparisons each edge becomes a transport along an equality of
morphisms, and the two sides of the pentagon become two such transports with the same source and
target. The edges drawn as equalities are straightened by the compatibility of the composition
comparison with a transport of its first morphism; the edges given by `α` need in addition the
associativity coherence, because the straightening brackets the triple composite the other way
round from `α`.

That argument uses nothing about the small étale topoi beyond the composition comparison
isomorphisms and their associativity coherence, so it is carried out for an arbitrary family of
pullback functors in the namespace `CategoryTheory` and then instantiated. This is not only for
generality: the small étale inverse image is built from an equivalence of topoi whose inverse
goes through `CategoryTheory.Functor.objPreimage`, so a sheaf in its image is a term no defeq
check may unfold, and a diagram chase performed on those objects does not typecheck. In the
abstract setting the objects are variables and the coherence argument is checked once.

For the same reason the cocycle condition is stated with the object-level identifications, whose
source and target write the iterated inverse images out as `m⁻¹(n⁻¹𝒢)` rather than as
`(n⁻¹ ⋙ m⁻¹)𝒢`. Every composition in the pentagon then joins two syntactically equal objects,
both in the abstract statement and in its instantiation, so no comparison of two spellings of a
sheaf is ever required. Stated with the functorial identifications instead, the pentagon's own
composability forces exactly that comparison, and the statement cannot be checked.

The hypotheses are exactly the assertions of the source's setting that the statement uses: that
`R` is `U ×_X U`, with `t` and `s` the two projections, is `IsPullback t s φ φ`, which is the
`isPullback` field of `AlgebraicGeometry.Space.Presentation`; that `R ×_{s, U, t} R` is the fibre
product of `s` and `t` is `IsPullback pr₀ pr₁ s t`; and the two identities relating `c` to the
projections are the `target_comp` and `source_comp` axioms of a groupoid,
`Stacks.Groupoids.GroupoidScheme`. Only the commutativity of the two cartesian squares is used,
and no étaleness hypothesis is needed for the construction, only for the setting to be a
presentation.

The declarations in the namespace `CategoryTheory` are general facts about a family of pullback
functors and belong with the bicategorical material on composition comparisons; they are here
only to keep that file untouched.

## References

* [Stacks Project, Tag 05YY](https://stacks.math.columbia.edu/tag/05YY)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 0263](https://stacks.math.columbia.edu/tag/0263)
* [Stacks Project, Tag 0233](https://stacks.math.columbia.edu/tag/0233)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

/-! ### Cocycle conditions for an abstract family of pullback functors -/

namespace CategoryTheory

universe v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] (A : C → Cat.{v₂, u₂})
  (P : {V W : C} → (V ⟶ W) → (A W ⥤ A V))
  (cmp : {V W Y : C} → (m : V ⟶ W) → (n : W ⟶ Y) → P (m ≫ n) ≅ P n ⋙ P m)

/-- The canonical identification of the two iterated pullbacks along composable pairs of
morphisms with the same composite: if `m₁ ≫ n₁ = m₂ ≫ n₂` then pulling back along `n₁` and then
`m₁` agrees with pulling back along `n₂` and then `m₂`.

Both sides are compared with the pullback along the common composite by the composition
comparison isomorphism. -/
def compIsoOfEq {V W Y : C} (m₁ m₂ : V ⟶ W) (n₁ n₂ : W ⟶ Y) (e : m₁ ≫ n₁ = m₂ ≫ n₂) :
    P n₁ ⋙ P m₁ ≅ P n₂ ⋙ P m₂ :=
  (cmp m₁ n₁).symm ≪≫ eqToIso (congrArg (fun k : V ⟶ Y => P k) e) ≪≫ cmp m₂ n₂

/-- The identification of `CategoryTheory.compIsoOfEq`, read on a single object: all four
iterated pullbacks are written out, so that the identification composes with the pullbacks of
other such identifications without any reassociation. -/
def compIsoOfEqApp {V W Y : C} (m₁ m₂ : V ⟶ W) (n₁ n₂ : W ⟶ Y) (e : m₁ ≫ n₁ = m₂ ≫ n₂)
    (G : A Y) : (P m₁).obj ((P n₁).obj G) ≅ (P m₂).obj ((P n₂).obj G) :=
  (compIsoOfEq A P cmp m₁ m₂ n₁ n₂ e).app G

/-- `CategoryTheory.compIsoOfEqApp` is the value of `CategoryTheory.compIsoOfEq` at an
object. -/
theorem compIsoOfEqApp_hom {V W Y : C} (m₁ m₂ : V ⟶ W) (n₁ n₂ : W ⟶ Y)
    (e : m₁ ≫ n₁ = m₂ ≫ n₂) (G : A Y) :
    (compIsoOfEqApp A P cmp m₁ m₂ n₁ n₂ e G).hom =
      (compIsoOfEq A P cmp m₁ m₂ n₁ n₂ e).hom.app G := rfl

/-- The composition comparison is compatible with a transport along an equality of its first
morphism. -/
@[reassoc]
private theorem cmp_transport_fst {V W Y : C} {m m' : V ⟶ W} (e : m = m') (n : W ⟶ Y) (F : A Y)
    (h₁ : (P n ⋙ P m).obj F = (P n ⋙ P m').obj F)
    (h₂ : (P (m ≫ n)).obj F = (P (m' ≫ n)).obj F) :
    (cmp m n).hom.app F ≫ eqToHom h₁ = eqToHom h₂ ≫ (cmp m' n).hom.app F := by
  subst e
  simp

/-- The composition comparison is compatible with a transport along an equality of its second
morphism. -/
@[reassoc]
private theorem cmp_transport_snd {V W Y : C} (m : V ⟶ W) {n n' : W ⟶ Y} (e : n = n') (F : A Y)
    (h₁ : (P n).obj F = (P n').obj F)
    (h₂ : (P (m ≫ n)).obj F = (P (m ≫ n')).obj F) :
    (cmp m n).hom.app F ≫ (P m).map (eqToHom h₁) =
      eqToHom h₂ ≫ (cmp m n').hom.app F := by
  subst e
  simp

/-- The iterated pullback of `(P p).obj F` along `n` and then `m`, compared with the pullback of
`F` along the composite `(m ≫ n) ≫ p`. -/
private def iteratedIso {V W Y Z : C} (m : V ⟶ W) (n : W ⟶ Y) (p : Y ⟶ Z) (F : A Z) :
    (P ((m ≫ n) ≫ p)).obj F ≅ (P m).obj ((P n).obj ((P p).obj F)) :=
  (cmp (m ≫ n) p).app F ≪≫ (cmp m n).app ((P p).obj F)

/-- The associativity coherence of a family of composition comparison isomorphisms: for three
composable morphisms, the two ways of comparing the thrice-iterated pullback with the pullback
along the triple composite agree. -/
def IsCompIsoCoherent : Prop :=
  ∀ {V W Y Z : C} (m : V ⟶ W) (n : W ⟶ Y) (p : Y ⟶ Z),
    (cmp m (n ≫ p)).hom ≫ Functor.whiskerRight (cmp n p).hom (P m) ≫
        (Functor.associator (P p) (P n) (P m)).hom ≫
          Functor.whiskerLeft (P p) (cmp m n).inv ≫ (cmp (m ≫ n) p).inv =
      eqToHom (congrArg (fun k : V ⟶ Z => P k) (Category.assoc m n p).symm)

/-- The straightening comparison, computed by first comparing the pullback along `n ≫ p` with
the iterated one and then pulling back along `m`: the two brackettings of the triple composite
agree, by the associativity coherence of the composition comparisons. -/
private theorem iteratedIso_hom (hcmp : IsCompIsoCoherent A P cmp) {V W Y Z : C} (m : V ⟶ W)
    (n : W ⟶ Y) (p : Y ⟶ Z) (F : A Z) :
    (iteratedIso A P cmp m n p F).hom =
      eqToHom (congrArg (fun k : V ⟶ Z => (P k).obj F) (Category.assoc m n p)) ≫
        (cmp m (n ≫ p)).hom.app F ≫ (P m).map ((cmp n p).hom.app F) := by
  have hco : (cmp m (n ≫ p)).hom.app F ≫ (P m).map ((cmp n p).hom.app F) ≫
      (cmp m n).inv.app ((P p).obj F) ≫ (cmp (m ≫ n) p).inv.app F =
      (eqToHom (congrArg (fun k : V ⟶ Z => P k) (Category.assoc m n p).symm)).app F := by
    have h := congrArg (fun τ => NatTrans.app τ F) (hcmp m n p)
    simpa using h
  have h : (cmp m (n ≫ p)).hom.app F ≫ (P m).map ((cmp n p).hom.app F) =
      (eqToHom (congrArg (fun k : V ⟶ Z => P k) (Category.assoc m n p).symm)).app F ≫
        (iteratedIso A P cmp m n p F).hom := by
    rw [← hco, iteratedIso]
    simp
  rw [h]
  simp [eqToHom_app]

/-- Against the straightening comparisons, an identification of iterated pullbacks along pairs
with the same composite becomes a transport along an equality of morphisms. -/
@[reassoc]
private theorem iteratedIso_hom_comp_compIsoOfEq {V W Y Z : C} (p : Y ⟶ Z) (m₁ m₂ : V ⟶ W)
    (n₁ n₂ : W ⟶ Y) (e : m₁ ≫ n₁ = m₂ ≫ n₂) (F : A Z) :
    (iteratedIso A P cmp m₁ n₁ p F).hom ≫
        (compIsoOfEq A P cmp m₁ m₂ n₁ n₂ e).hom.app ((P p).obj F) =
      eqToHom (congrArg (fun k : V ⟶ Y => (P (k ≫ p)).obj F) e) ≫
        (iteratedIso A P cmp m₂ n₂ p F).hom := by
  rw [iteratedIso, iteratedIso, compIsoOfEq]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Iso.app_hom,
    eqToIso.hom, Category.assoc, eqToHom_app, Iso.hom_inv_id_app_assoc]
  rw [cmp_transport_fst_assoc A P cmp e p F _
    (congrArg (fun k : V ⟶ Y => (P (k ≫ p)).obj F) e)]

/-- Against the straightening comparisons, pulling back along `m` the identification coming from
`t ≫ p = s ≫ p` becomes a transport along an equality of morphisms. -/
@[reassoc]
private theorem iteratedIso_hom_comp_map (hcmp : IsCompIsoCoherent A P cmp) {V W Y Z : C}
    (p : Y ⟶ Z) (s t : W ⟶ Y) (hst : t ≫ p = s ≫ p) (m : V ⟶ W) (F : A Z) :
    (iteratedIso A P cmp m t p F).hom ≫
        (P m).map ((compIsoOfEq A P cmp t s p p hst).hom.app F) =
      eqToHom (congrArg (fun k : V ⟶ Z => (P k).obj F)
          ((Category.assoc m t p).trans
            ((congrArg (fun k : W ⟶ Z => m ≫ k) hst).trans
              (Category.assoc m s p).symm))) ≫
        (iteratedIso A P cmp m s p F).hom := by
  rw [iteratedIso_hom A P cmp hcmp, iteratedIso_hom A P cmp hcmp, compIsoOfEq]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    eqToIso.hom, Category.assoc, eqToHom_app, ← Functor.map_comp, Iso.hom_inv_id_app_assoc]
  rw [Functor.map_comp, cmp_transport_snd_assoc A P cmp m hst F _
    (congrArg (fun k : W ⟶ Z => (P (m ≫ k)).obj F) hst)]
  simp

/-- **The cocycle condition.** Let `p : U ⟶ X`, let `s, t : R ⟶ U` satisfy `t ≫ p = s ≫ p`, and
let `pr₀, pr₁, c : R₂ ⟶ R` satisfy `pr₀ ≫ s = pr₁ ≫ t`, `pr₀ ≫ t = c ≫ t` and
`pr₁ ≫ s = c ≫ s`. Writing `α` for the identification of the pullback of `(P p).obj F` along `t`
with its pullback along `s` coming from `t ≫ p = s ≫ p`, the pentagon formed by the pullbacks of
`α` along `pr₀`, `pr₁` and `c` together with the three identifications of iterated pullbacks
along pairs with the same composite commutes. -/
private theorem compIsoOfEq_cocycle (hcmp : IsCompIsoCoherent A P cmp) {X U R R₂ : C}
    (p : U ⟶ X)
    (s t : R ⟶ U) (hst : t ≫ p = s ≫ p)
    (pr₀ pr₁ c : R₂ ⟶ R) (hfib : pr₀ ≫ s = pr₁ ≫ t) (hct : pr₀ ≫ t = c ≫ t)
    (hcs : pr₁ ≫ s = c ≫ s) (F : A X) :
    (P pr₀).map ((compIsoOfEq A P cmp t s p p hst).hom.app F) ≫
        (compIsoOfEq A P cmp pr₀ pr₁ s t hfib).hom.app ((P p).obj F) ≫
        (P pr₁).map ((compIsoOfEq A P cmp t s p p hst).hom.app F) ≫
        (compIsoOfEq A P cmp pr₁ c s s hcs).hom.app ((P p).obj F) =
      (compIsoOfEq A P cmp pr₀ c t t hct).hom.app ((P p).obj F) ≫
        (P c).map ((compIsoOfEq A P cmp t s p p hst).hom.app F) := by
  rw [← Iso.cancel_iso_hom_left (iteratedIso A P cmp pr₀ t p F),
    iteratedIso_hom_comp_map_assoc A P cmp hcmp p s t hst pr₀ F,
    iteratedIso_hom_comp_compIsoOfEq_assoc A P cmp p pr₀ pr₁ s t hfib F,
    iteratedIso_hom_comp_map_assoc A P cmp hcmp p s t hst pr₁ F,
    iteratedIso_hom_comp_compIsoOfEq A P cmp p pr₁ c s s hcs F,
    iteratedIso_hom_comp_compIsoOfEq_assoc A P cmp p pr₀ c t t hct F,
    iteratedIso_hom_comp_map A P cmp hcmp p s t hst c F]
  simp

/-- **The cocycle condition**, read on a single object. Let `p : U ⟶ X`, let `s, t : R ⟶ U`
satisfy `t ≫ p = s ≫ p`, and let `pr₀, pr₁, c : R₂ ⟶ R` satisfy `pr₀ ≫ s = pr₁ ≫ t`,
`pr₀ ≫ t = c ≫ t` and `pr₁ ≫ s = c ≫ s`. Writing `α` for the identification of the pullback of
`G = (P p).obj F` along `t` with its pullback along `s` coming from `t ≫ p = s ≫ p`, the pentagon
formed by the pullbacks of `α` along `pr₀`, `pr₁` and `c` together with the three identifications
of iterated pullbacks along pairs with the same composite commutes. -/
theorem compIsoOfEqApp_cocycle (hcmp : IsCompIsoCoherent A P cmp) {X U R R₂ : C} (p : U ⟶ X)
    (s t : R ⟶ U) (hst : t ≫ p = s ≫ p) (pr₀ pr₁ c : R₂ ⟶ R) (hfib : pr₀ ≫ s = pr₁ ≫ t)
    (hct : pr₀ ≫ t = c ≫ t) (hcs : pr₁ ≫ s = c ≫ s) (F : A X) :
    (P pr₀).map (compIsoOfEqApp A P cmp t s p p hst F).hom ≫
        (compIsoOfEqApp A P cmp pr₀ pr₁ s t hfib ((P p).obj F)).hom ≫
        (P pr₁).map (compIsoOfEqApp A P cmp t s p p hst F).hom ≫
        (compIsoOfEqApp A P cmp pr₁ c s s hcs ((P p).obj F)).hom =
      (compIsoOfEqApp A P cmp pr₀ c t t hct ((P p).obj F)).hom ≫
        (P c).map (compIsoOfEqApp A P cmp t s p p hst F).hom :=
  compIsoOfEq_cocycle A P cmp hcmp p s t hst pr₀ pr₁ c hfib hct hcs F

end CategoryTheory

/-! ### The canonical isomorphism of a presentation and its cocycle condition -/

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X U R R₂ : AlgebraicSpaces B S hS}

/-- The canonical identification of two iterated small étale inverse images along composable
pairs of morphisms of algebraic spaces with the same composite: if `m₁ ≫ n₁ = m₂ ≫ n₂` then
pulling back along `n₁` and then `m₁` agrees with pulling back along `n₂` and then `m₂`.

Both sides are compared with the inverse image along the common composite by the composition
isomorphism of Stacks 03G2, part (3). -/
noncomputable def inverseImageCompIsoOfEq (m₁ m₂ : R₂ ⟶ R) (n₁ n₂ : R ⟶ U)
    (e : m₁ ≫ n₁ = m₂ ≫ n₂) :
    smallEtaleSheafInverseImage B S hS n₁ ⋙ smallEtaleSheafInverseImage B S hS m₁ ≅
      smallEtaleSheafInverseImage B S hS n₂ ⋙ smallEtaleSheafInverseImage B S hS m₂ :=
  compIsoOfEq (smallEtaleSheafCat B S hS) (@smallEtaleSheafInverseImage B S hS)
    (@smallToposMorphism_comp_inverseImage B S hS) m₁ m₂ n₁ n₂ e

/-- **Stacks 05YY.** Let `φ : U ⟶ X` be a morphism of algebraic spaces with `R = U ×_X U` and
`t, s : R ⟶ U` the two projections, as for a presentation of `X` by a surjective étale `φ`. For
a sheaf `ℱ` on the small étale site of `X`, the sheaf `𝒢 = φ⁻¹ℱ` on the small étale site of `U`
carries a canonical isomorphism

`α : t⁻¹𝒢 ⟶ s⁻¹𝒢`,

natural in `ℱ`.

It is the identification of the two iterated inverse images along `(t, φ)` and along `(s, φ)`,
whose composites agree because `R` is the fibre product of `φ` with itself. -/
@[stacks 05YY "the canonical isomorphism and its cocycle condition"]
noncomputable def presentationPullbackIso (φ : U ⟶ X) (s t : R ⟶ U)
    (hR : IsPullback t s φ φ) :
    smallEtaleSheafInverseImage B S hS φ ⋙ smallEtaleSheafInverseImage B S hS t ≅
      smallEtaleSheafInverseImage B S hS φ ⋙ smallEtaleSheafInverseImage B S hS s :=
  inverseImageCompIsoOfEq B S hS t s φ φ hR.w

/-- The identification of `AlgebraicGeometry.Space.inverseImageCompIsoOfEq`, read on a single
sheaf: the two iterated small étale inverse images of `𝒢` are written out, so that this
identification composes with the inverse images of other such identifications without any
reassociation. By construction it is the value of
`AlgebraicGeometry.Space.inverseImageCompIsoOfEq` at `𝒢`, which is
`CategoryTheory.compIsoOfEqApp_hom`. -/
noncomputable def inverseImageCompIsoOfEqApp (m₁ m₂ : R₂ ⟶ R) (n₁ n₂ : R ⟶ U)
    (e : m₁ ≫ n₁ = m₂ ≫ n₂) (G : smallEtaleSheafCat B S hS U) :
    (smallEtaleSheafInverseImage B S hS m₁).obj
        ((smallEtaleSheafInverseImage B S hS n₁).obj G) ≅
      (smallEtaleSheafInverseImage B S hS m₂).obj
        ((smallEtaleSheafInverseImage B S hS n₂).obj G) :=
  compIsoOfEqApp (smallEtaleSheafCat B S hS) (@smallEtaleSheafInverseImage B S hS)
    (@smallToposMorphism_comp_inverseImage B S hS) m₁ m₂ n₁ n₂ e G

/-- **Stacks 05YY.** The isomorphism

`α : t⁻¹𝒢 ⟶ s⁻¹𝒢`

canonically attached to the sheaf `𝒢 = φ⁻¹ℱ`, for `φ : U ⟶ X` with `R = U ×_X U` and
`t, s : R ⟶ U` the two projections, as for a presentation of `X` by a surjective étale `φ`.

By construction it is the value at `ℱ` of the natural isomorphism
`AlgebraicGeometry.Space.presentationPullbackIso`. -/
@[stacks 05YY "the canonical isomorphism and its cocycle condition"]
noncomputable def presentationPullbackIsoApp (φ : U ⟶ X) (s t : R ⟶ U)
    (hR : IsPullback t s φ φ) (F : smallEtaleSheafCat B S hS X) :
    (smallEtaleSheafInverseImage B S hS t).obj
        ((smallEtaleSheafInverseImage B S hS φ).obj F) ≅
      (smallEtaleSheafInverseImage B S hS s).obj
        ((smallEtaleSheafInverseImage B S hS φ).obj F) :=
  inverseImageCompIsoOfEqApp B S hS t s φ φ hR.w F

/-- **Stacks 05YY.** The cocycle condition on `α`. Let `R₂ = R ×_{s, U, t} R` be the fibre
product of `s` and `t`, with projections `pr₀` and `pr₁`, and let `c : R₂ ⟶ R` be the
composition law of the groupoid, so that `c` has the target of the first arrow and the source of
the second. Then the pentagon

`pr₀⁻¹t⁻¹𝒢 → pr₀⁻¹s⁻¹𝒢 = pr₁⁻¹t⁻¹𝒢 → pr₁⁻¹s⁻¹𝒢 = c⁻¹s⁻¹𝒢`,
`pr₀⁻¹t⁻¹𝒢 = c⁻¹t⁻¹𝒢 → c⁻¹s⁻¹𝒢`

commutes: its three arrows are `pr₀⁻¹α`, `pr₁⁻¹α` and `c⁻¹α`, and its three equalities are the
canonical identifications of iterated inverse images along pairs with the same composite.

This is `CategoryTheory.compIsoOfEqApp_cocycle` for the small étale inverse images, whose
associativity coherence is
`AlgebraicGeometry.Space.smallToposMorphism_comp_inverseImage_assoc`. -/
@[stacks 05YY "the canonical isomorphism and its cocycle condition"]
theorem presentationPullbackIsoApp_cocycle (φ : U ⟶ X) (s t : R ⟶ U) (hR : IsPullback t s φ φ)
    (pr₀ pr₁ c : R₂ ⟶ R) (hR₂ : IsPullback pr₀ pr₁ s t) (hct : pr₀ ≫ t = c ≫ t)
    (hcs : pr₁ ≫ s = c ≫ s) (F : smallEtaleSheafCat B S hS X) :
    (smallEtaleSheafInverseImage B S hS pr₀).map
          (presentationPullbackIsoApp B S hS φ s t hR F).hom ≫
        (inverseImageCompIsoOfEqApp B S hS pr₀ pr₁ s t hR₂.w
          ((smallEtaleSheafInverseImage B S hS φ).obj F)).hom ≫
        (smallEtaleSheafInverseImage B S hS pr₁).map
          (presentationPullbackIsoApp B S hS φ s t hR F).hom ≫
        (inverseImageCompIsoOfEqApp B S hS pr₁ c s s hcs
          ((smallEtaleSheafInverseImage B S hS φ).obj F)).hom =
      (inverseImageCompIsoOfEqApp B S hS pr₀ c t t hct
          ((smallEtaleSheafInverseImage B S hS φ).obj F)).hom ≫
        (smallEtaleSheafInverseImage B S hS c).map
          (presentationPullbackIsoApp B S hS φ s t hR F).hom :=
  compIsoOfEqApp_cocycle (smallEtaleSheafCat B S hS) (@smallEtaleSheafInverseImage B S hS)
    (@smallToposMorphism_comp_inverseImage B S hS)
    (@smallToposMorphism_comp_inverseImage_assoc B S hS)
    φ s t hR.w pr₀ pr₁ c hR₂.w hct hcs F

end AlgebraicGeometry.Space

end
