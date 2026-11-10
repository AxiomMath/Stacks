module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassScale

/-!
# The base change of Tag 01NT for the union `F` of the display 01NX

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN), and
`g : S' ⟶ S` a morphism of schemes; write `𝒜' = g^*𝒜` for the base-changed algebra
`...RelativeProjQcohSheaf.baseAlgebra`.  Tag 01NT compares the functors of quadruples of the two
situations **at a fixed degree**: `...RelativeProjQcohSheaf.Fd.isLimitBaseChangeCone` exhibits
`F'_d` as a limit of the cospan `h_{S'} ⟶ h_S ⟵ F_d`.

This file proves the same for the **union** `F = ⋃_{d ≥ 1} F_d` of the display 01NX, which the
note at `...RelativeProjQcohSheaf.Fd.isLimitBaseChangeCone` records as not proved:
`...RelativeProjQcohSheaf.F.isLimitBaseChangeCone` exhibits `F'` as a limit of the cospan
`h_{S'} ⟶ h_S ⟵ F`, and `...RelativeProjQcohSheaf.F.baseChangePullbackIso` reads that off as the
canonical isomorphism `F' ≅ h_{S'} ×_{h_S} F`.

## How

The bijection on quadruples is Tag 01NT's own, `...RelativeProjQcohSheaf.Quadruple.baseChangeUp`
and `...Quadruple.baseChangeDown`: the invertible module is untouched and `ψ` is carried across
the canonical identification `(f')^*(𝒜')^{(d)} = f^*𝒜^{(d)}`.  It preserves the degree, so the
only thing to check is that it matches the two relations `...RelativeProjQcohSheaf.UnionRel`
generates:

* inside one degree, strict equivalence — already an iff, by
  `...RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_baseChangeUp_iff`;
* across degrees, the equivalence of Tag 01NW — one direction of which is already proved, as
  `...RelativeProjQcohSheaf.Quadruple.CompatibleAt.baseChangeUp`.

So the work here is the **converse** of that last one, which the library did not have.  It is
`...RelativeProjQcohSheaf.Quadruple.compatibleAt_baseChangeUp_iff`, and it is the same
cancellation that proves the fixed-degree strict-equivalence iff: the identification of Tag 01NT
is an isomorphism, so it can be cancelled off the left of the `ψ`-clause, and
`...RelativeProjQcohSheaf.Quadruple.compComparison_comp_eqToHom` moves it across the transport of
the degree.  With the iff in hand the base change descends to the quotient in both directions,
and the limit statement is assembled exactly as the fixed-degree one is.

Everything is unconditional: no positivity of the degree, no hypothesis on `g`, no
quasi-compactness of the test scheme.

## References

* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NT](https://stacks.math.columbia.edu/tag/01NT)
* [Stacks Project, Tag 01NW](https://stacks.math.columbia.edu/tag/01NW)
* [Stacks Project, Tag 01NX](https://stacks.math.columbia.edu/tag/01NX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

/-! ### A comparison of Tag 01NW survives the base change in both directions -/

namespace Quadruple

variable {S S' T : Scheme.{u}} (g : S' ⟶ S) (f' : T ⟶ S')
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) {d d' : ℤ}

/-- The cancellation the `ψ`-clause of a comparison needs to come back **down** across the base
change: an epimorphism cancelled off the left, with the morphism attached to the degree moved
across it.  This is the converse of the rearrangement
`...RelativeProjQcohSheaf.Quadruple.CompatibleAt.baseChangeUp` performs, and it is stated with
every object and morphism a free variable for the same reason — so that a caller can discharge
it by `exact` where two spellings of an object are equal but not syntactically so. -/
private theorem comp_app_comp_cancel {C : Type*} [Category C] {W W' X X' Y Y' : C}
    (c : W ⟶ X) [Epi c] (α : X ⟶ Y) (β : X' ⟶ Y') (κ : Y ⟶ Y') (e : X ⟶ X') (ε : W ⟶ W')
    (c' : W' ⟶ X') (hcomm : c ≫ e = ε ≫ c') (hup : c ≫ α ≫ κ = ε ≫ c' ≫ β) :
    α ≫ κ = e ≫ β := by
  refine (cancel_epi c).mp (hup.trans ?_)
  rw [← Category.assoc, ← hcomm, Category.assoc]

/-- **A comparison of [Stacks, Tag 01NW] at a common multiple of two degrees survives the base
change of [Stacks, Tag 01NT] in both directions.**

The base change leaves the invertible module of a quadruple unchanged, so a comparison on either
side is carried by *the same* family of isomorphisms of the Laurent algebras, and its
multiplicativity and unit clauses are the other side's verbatim.  Only the clause about `ψ`
moves, and it moves by an isomorphism: the identification of Tag 01NT, which
`...RelativeProjQcohSheaf.Quadruple.compComparison_comp_eqToHom` commutes with the transport of
the degree.

The `←` direction is `...RelativeProjQcohSheaf.Quadruple.CompatibleAt.baseChangeUp`; the `→`
direction is the cancellation of that identification. -/
theorem compatibleAt_baseChangeUp_iff {P : Quadruple f' (baseAlgebra g A) d}
    {Q : Quadruple f' (baseAlgebra g A) d'} {a a' : ℤ} :
    CompatibleAt (P.baseChangeUp g f' A d) (Q.baseChangeUp g f' A d') a a' ↔
      CompatibleAt P Q a a' := by
  refine ⟨fun hc => ?_, fun hc => hc.baseChangeUp g f' A⟩
  obtain ⟨hm, γ, hmul, hone, hψ⟩ := hc
  refine ⟨hm, γ, hmul, hone, fun p q hpq => ?_⟩
  have hiso : IsIso (compComparison f' g (A.piece (p * d))) := isIso_compComparison f' g _
  have : Epi (compComparison f' g (A.piece (p * d))) := IsIso.epi_of_iso _
  exact comp_app_comp_cancel (compComparison f' g (A.piece (p * d))) (P.twisting.app p)
    (Q.twisting.app q) (γ p q hpq).hom
    ((pullbackFunctor (ringedSpaceHom f')).map
      (eqToHom (congrArg (baseAlgebra g A).piece (hpq.degree_eq hm))))
    ((pullbackFunctor (ringedSpaceHom (f' ≫ g))).map
      (eqToHom (congrArg A.piece (hpq.degree_eq hm))))
    (compComparison f' g (A.piece (q * d')))
    (compComparison_comp_eqToHom g f' A (hpq.degree_eq hm)) (hψ p q hpq)

/-- **A comparison of [Stacks, Tag 01NW] survives the base change of [Stacks, Tag 01NT] in the
other direction**: it is the forward reading of
`...RelativeProjQcohSheaf.Quadruple.compatibleAt_baseChangeUp_iff` at the quadruples the base
change carries down, which it carries back up to the given ones. -/
theorem CompatibleAt.baseChangeDown {P : Quadruple (f' ≫ g) A d} {Q : Quadruple (f' ≫ g) A d'}
    {a a' : ℤ} (hc : CompatibleAt P Q a a') :
    CompatibleAt (P.baseChangeDown g f' A d) (Q.baseChangeDown g f' A d') a a' := by
  refine (compatibleAt_baseChangeUp_iff g f' A).mp ?_
  rw [baseChangeUp_baseChangeDown, baseChangeUp_baseChangeDown]
  exact hc

/-- **The equivalence of [Stacks, Section 01NS] across degrees survives the base change of
[Stacks, Tag 01NT]**, in the spelling the union's relation uses.  Equivalence *is* a comparison
at the common multiple `d d'` of the two degrees, so this is
`...RelativeProjQcohSheaf.Quadruple.compatibleAt_baseChangeUp_iff` read at `(d', d)`. -/
theorem equivalent_baseChangeUp_iff {P : Quadruple f' (baseAlgebra g A) d}
    {Q : Quadruple f' (baseAlgebra g A) d'} :
    Equivalent (P.baseChangeUp g f' A d) (Q.baseChangeUp g f' A d') ↔ Equivalent P Q :=
  compatibleAt_baseChangeUp_iff g f' A

/-- The equivalence of [Stacks, Section 01NS] across degrees survives the base change of
[Stacks, Tag 01NT] in the other direction. -/
theorem Equivalent.baseChangeDown {P : Quadruple (f' ≫ g) A d} {Q : Quadruple (f' ≫ g) A d'}
    (h : Equivalent P Q) :
    Equivalent (P.baseChangeDown g f' A d) (Q.baseChangeDown g f' A d') :=
  CompatibleAt.baseChangeDown g f' A h

end Quadruple

/-! ### The base-change map on the union `F`, and the fibre product -/

section FLevel

variable {S S' : Scheme.{u}} (g : S' ⟶ S)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace))

/-- Two morphisms of presheaves of types on schemes are equal when they agree on every element. -/
private theorem natTrans_ext_of_apply_eq {X Y : Scheme.{u}ᵒᵖ ⥤ Type (u + 1)} {α β : X ⟶ Y}
    (h : ∀ T x, α.app T x = β.app T x) : α = β :=
  NatTrans.ext (funext fun T => TypeCat.homEquiv.injective (funext (h T)))

/-- **The map `F'(T) → F(T)` of the union.** A point of `F'(T)` is a morphism `f' : T ⟶ S'`
together with the class of a quadruple of positive degree for the base-changed situation
`(S', 𝒜')`; it is sent to the morphism `g ∘ f'` together with the class of the corresponding
quadruple for `(S, 𝒜)`, which has the same degree.

It is well defined because the bijection on quadruples matches *both* relations the union's
`...RelativeProjQcohSheaf.UnionRel` generates: strict equivalence inside a degree by
`...RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_baseChangeUp_iff`, and the equivalence of
Tag 01NW across degrees by
`...RelativeProjQcohSheaf.Quadruple.equivalent_baseChangeUp_iff`. -/
def F.baseChangeUp {T : Scheme.{u}} (ξ : F (baseAlgebra g A) T) : F A T :=
  ⟨ξ.1 ≫ g,
    Quot.lift
      (fun P : PositiveQuadruple ξ.1 (baseAlgebra g A) =>
        Quot.mk (UnionRel (f := ξ.1 ≫ g) (A := A)) ⟨P.1, P.2.baseChangeUp g ξ.1 A P.1.1⟩)
      (fun _ _ hrel => by
        cases hrel with
        | strict hs =>
            exact Quot.sound (UnionRel.strict
              ((Quadruple.strictlyEquivalent_baseChangeUp_iff g ξ.1 A _).mpr hs))
        | equivalent he =>
            exact Quot.sound (UnionRel.equivalent
              ((Quadruple.equivalent_baseChangeUp_iff g ξ.1 A).mpr he)))
      ξ.2⟩

/-- The morphism to `S` recorded by the image of a point of `F'(T)` is the composite with `g`. -/
@[simp] theorem F.baseChangeUp_fst {T : Scheme.{u}} (ξ : F (baseAlgebra g A) T) :
    (F.baseChangeUp g A ξ).1 = ξ.1 ≫ g := rfl

/-- The map sends the point of a quadruple to the point of the corresponding quadruple, of the
same degree. -/
@[simp] theorem F.baseChangeUp_mk {T : Scheme.{u}} (f' : T ⟶ S') {d : ℤ} (hd : 0 < d)
    (P : Quadruple f' (baseAlgebra g A) d) :
    F.baseChangeUp g A (F.mk f' hd P) = F.mk (f' ≫ g) hd (P.baseChangeUp g f' A d) := rfl

/-- **The inverse map on the union, over a fixed factorization**: the class of a quadruple of
positive degree for `(S, 𝒜)` over `g ∘ f'` gives a point of `F'(T)` over `f'`.  Well defined by
the other readings of the same two iffs, which are
`...RelativeProjQcohSheaf.Quadruple.strictlyEquivalent_baseChangeDown` and
`...RelativeProjQcohSheaf.Quadruple.Equivalent.baseChangeDown`. -/
def F.baseChangeDownQ {T : Scheme.{u}} (f' : T ⟶ S')
    (q : Quot (UnionRel (f := f' ≫ g) (A := A))) : F (baseAlgebra g A) T :=
  ⟨f',
    Quot.lift
      (fun P : PositiveQuadruple (f' ≫ g) A =>
        Quot.mk (UnionRel (f := f') (A := baseAlgebra g A))
          ⟨P.1, P.2.baseChangeDown g f' A P.1.1⟩)
      (fun _ _ hrel => by
        cases hrel with
        | strict hs =>
            exact Quot.sound (UnionRel.strict
              (Quadruple.strictlyEquivalent_baseChangeDown g f' A _ hs))
        | equivalent he =>
            exact Quot.sound (UnionRel.equivalent
              (Quadruple.Equivalent.baseChangeDown g f' A he)))
      q⟩

/-- The morphism to `S'` recorded by the inverse map is the chosen factorization. -/
@[simp] theorem F.baseChangeDownQ_fst {T : Scheme.{u}} (f' : T ⟶ S')
    (q : Quot (UnionRel (f := f' ≫ g) (A := A))) :
    (F.baseChangeDownQ g A f' q).1 = f' := rfl

/-- The two maps on the union are inverse, in one direction. -/
theorem F.baseChangeUp_baseChangeDownQ {T : Scheme.{u}} (f' : T ⟶ S')
    (q : Quot (UnionRel (f := f' ≫ g) (A := A))) :
    F.baseChangeUp g A (F.baseChangeDownQ g A f' q) = ⟨f' ≫ g, q⟩ := by
  induction q using Quot.ind with
  | _ P =>
      exact congrArg
        (fun R : Quadruple (f' ≫ g) A P.1.1 =>
          (⟨f' ≫ g, Quot.mk (UnionRel (f := f' ≫ g) (A := A)) ⟨P.1, R⟩⟩ : F A T))
        (Quadruple.baseChangeUp_baseChangeDown g f' A P.1.1 P.2)

/-- The two maps on the union are inverse, in the other direction. -/
theorem F.baseChangeDownQ_baseChangeUp {T : Scheme.{u}} (ξ : F (baseAlgebra g A) T) :
    F.baseChangeDownQ g A ξ.1 (F.baseChangeUp g A ξ).2 = ξ := by
  obtain ⟨f', q⟩ := ξ
  induction q using Quot.ind with
  | _ P =>
      exact congrArg
        (fun R : Quadruple f' (baseAlgebra g A) P.1.1 =>
          (⟨f', Quot.mk (UnionRel (f := f') (A := baseAlgebra g A)) ⟨P.1, R⟩⟩ :
            F (baseAlgebra g A) T))
        (Quadruple.baseChangeDown_baseChangeUp g f' A P.1.1 P.2)

/-- **The map `F'(T) → F(T)` commutes with the pullback along a morphism of test schemes.**
This is `...RelativeProjQcohSheaf.Quadruple.baseChangeUp_pullback` descended to the union. -/
theorem F.baseChangeUp_pullback {T T₃ : Scheme.{u}} (k : T₃ ⟶ T)
    (ξ : F (baseAlgebra g A) T) :
    F.baseChangeUp g A (F.pullback k ξ) = F.pullback k (F.baseChangeUp g A ξ) := by
  obtain ⟨f', q⟩ := ξ
  induction q using Quot.ind with
  | _ P =>
      exact (congrArg
        (fun R : Quadruple ((k ≫ f') ≫ g) A P.1.1 =>
          (⟨(k ≫ f') ≫ g, Quot.mk (UnionRel (f := (k ≫ f') ≫ g) (A := A)) ⟨P.1, R⟩⟩ : F A T₃))
        (Quadruple.baseChangeUp_pullback g f' A P.1.1 P.2 k)).symm

/-- **The canonical natural transformation `F' ⟹ F` of the union**, the map of functors over
`g`: on a test scheme it is `...RelativeProjQcohSheaf.F.baseChangeUp`, and naturality is
`...RelativeProjQcohSheaf.F.baseChangeUp_pullback`. -/
def F.baseChangeNat : F.functor (baseAlgebra g A) ⟶ F.functor A where
  app _T := TypeCat.ofHom (F.baseChangeUp g A)
  naturality _ _ φ := TypeCat.homEquiv.injective (funext fun ξ =>
    F.baseChangeUp_pullback g A φ.unop ξ)

/-- The components of the canonical natural transformation. -/
@[simp] theorem F.baseChangeNat_app (T : Scheme.{u}ᵒᵖ) (ξ : F (baseAlgebra g A) T.unop) :
    (F.baseChangeNat g A).app T ξ = F.baseChangeUp g A ξ := rfl

/-- **The square defining the comparison commutes**: the structure morphism recorded by a point
of `F'(T)`, composed with `g`, is the structure morphism recorded by its image in `F(T)`. -/
theorem F.toBase_comp_yonedaBaseMap :
    F.toBase (baseAlgebra g A) ≫ yonedaBaseMap g = F.baseChangeNat g A ≫ F.toBase A :=
  natTrans_ext_of_apply_eq fun _ _ => rfl

/-- **The fibre product `h_{S'} ×_{h_S} F` written out.** Its value on a test scheme `T` is the
set of pairs consisting of a morphism `f' : T ⟶ S'` and a point of `F(T)` whose structure
morphism is `g ∘ f'`, and a morphism of test schemes acts by composition and by the pullback of
a point of the union. -/
def F.baseFibre : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj T := {p : ULift.{u + 1, u} (T.unop ⟶ S') × F A T.unop // p.1.down ≫ g = p.2.1}
  map {_X _Y} φ := TypeCat.ofHom fun p =>
    ⟨(ULift.up (φ.unop ≫ p.1.1.down), F.pullback φ.unop p.1.2), by
      rw [F.pullback_fst, Category.assoc, p.2]⟩
  map_id _ := TypeCat.homEquiv.injective (funext fun p =>
    Subtype.ext (Prod.ext (congrArg ULift.up (Category.id_comp p.1.1.down))
      (F.pullback_id p.1.2)))
  map_comp φ χ := TypeCat.homEquiv.injective (funext fun p =>
    Subtype.ext (Prod.ext (congrArg ULift.up (Category.assoc χ.unop φ.unop p.1.1.down))
      (F.pullback_comp φ.unop χ.unop p.1.2)))

/-- The projection of the fibre product to the functor of points of the new base. -/
def F.baseFibreFst :
    F.baseFibre g A ⟶ yoneda.obj S' ⋙ uliftFunctor.{u + 1, u} where
  app _T := TypeCat.ofHom fun p => p.1.1
  naturality _ _ _ := TypeCat.homEquiv.injective (funext fun _p => rfl)

/-- The projection of the fibre product to `F`. -/
def F.baseFibreSnd : F.baseFibre g A ⟶ F.functor A where
  app _T := TypeCat.ofHom fun p => p.1.2
  naturality _ _ _ := TypeCat.homEquiv.injective (funext fun _p => rfl)

/-- The two projections of the fibre product agree over `h_S`. -/
theorem F.baseFibre_condition :
    F.baseFibreFst g A ≫ yonedaBaseMap g = F.baseFibreSnd g A ≫ F.toBase A :=
  NatTrans.ext (funext fun _T => TypeCat.homEquiv.injective (funext fun p =>
    congrArg ULift.up p.2))

/-- The commutativity condition of a cone over the cospan `h_{S'} ⟶ h_S ⟵ F`, read on an
element of the vertex. -/
theorem F.baseFibre_cone_condition
    (s : PullbackCone (yonedaBaseMap g) (F.toBase A)) (T : Scheme.{u}ᵒᵖ) (w : s.pt.obj T) :
    (s.fst.app T w).down ≫ g = (s.snd.app T w).1 := by
  have h : (yonedaBaseMap g).app T (s.fst.app T w) = (F.toBase A).app T (s.snd.app T w) :=
    ConcreteCategory.congr_hom
      (congrArg (fun α : s.pt ⟶ yoneda.obj S ⋙ uliftFunctor.{u + 1, u} => α.app T)
        s.condition) w
  exact congrArg ULift.down h

/-- The morphism into the fibre product determined by a cone over the cospan
`h_{S'} ⟶ h_S ⟵ F`: on an element of the vertex it is the pair of its two images. -/
def F.baseFibreLift (s : PullbackCone (yonedaBaseMap g) (F.toBase A)) :
    s.pt ⟶ F.baseFibre g A where
  app T := TypeCat.ofHom fun w =>
    ⟨(s.fst.app T w, s.snd.app T w), F.baseFibre_cone_condition g A s T w⟩
  naturality _ _ φ := TypeCat.homEquiv.injective (funext fun w =>
    Subtype.ext (Prod.ext (natTrans_app_map s.fst φ w) (natTrans_app_map s.snd φ w)))

/-- **`F.baseFibre` with its two projections is the fibre product `h_{S'} ×_{h_S} F`.** The
limit is checked directly: a cone over the cospan is a pair of compatible maps, which is a map
into the set of compatible pairs. -/
def F.isLimitBaseFibre :
    IsLimit (PullbackCone.mk (F.baseFibreFst g A) (F.baseFibreSnd g A)
      (F.baseFibre_condition g A)) :=
  PullbackCone.IsLimit.mk _ (fun s => F.baseFibreLift g A s)
    (fun _ => NatTrans.ext (funext fun _T =>
      TypeCat.homEquiv.injective (funext fun _w => rfl)))
    (fun _ => NatTrans.ext (funext fun _T =>
      TypeCat.homEquiv.injective (funext fun _w => rfl)))
    (fun _ m h1 h2 => NatTrans.ext (funext fun T =>
      TypeCat.homEquiv.injective (funext fun w => by
        refine Subtype.ext (Prod.ext ?_ ?_)
        · exact ConcreteCategory.congr_hom
            (congrArg (fun α : _ ⟶ yoneda.obj S' ⋙ uliftFunctor.{u + 1, u} => α.app T) h1) w
        · exact ConcreteCategory.congr_hom
            (congrArg (fun α : _ ⟶ F.functor A => α.app T) h2) w)))

/-- The inverse map on the union, applied to a point of `F(T)` whose structure morphism factors
through `S'`, returns that point.  The class is transported along the factorization, which is the
only transport the comparison needs. -/
theorem F.baseChangeUp_baseChangeDownQ_cast {T : Scheme.{u}} (f' : T ⟶ S') (ξ : F A T)
    (h : f' ≫ g = ξ.1) :
    F.baseChangeUp g A (F.baseChangeDownQ g A f'
        (cast (congrArg (fun f => Quot (UnionRel (f := f) (A := A))) h.symm) ξ.2)) = ξ := by
  obtain ⟨f, q⟩ := ξ
  obtain rfl : f' ≫ g = f := h
  exact F.baseChangeUp_baseChangeDownQ g A f' q

/-- **The base change of the union on a single test scheme: `F'(T)` is the fibre product of the
morphisms `T ⟶ S'` with `F(T)` over the morphisms `T ⟶ S`.** A point of `F'(T)` is a morphism
`f' : T ⟶ S'` together with the class of a quadruple of positive degree over `f'` for
`(S', 𝒜')`, and the bijection on quadruples turns the latter into the class of a quadruple of
the same degree over `g ∘ f'` for `(S, 𝒜)`. -/
def F.baseFibreEquiv (T : Scheme.{u}) :
    F (baseAlgebra g A) T ≃
      {p : ULift.{u + 1, u} (T ⟶ S') × F A T // p.1.down ≫ g = p.2.1} where
  toFun ξ := ⟨(ULift.up ξ.1, F.baseChangeUp g A ξ), rfl⟩
  invFun p := F.baseChangeDownQ g A p.1.1.down
    (cast (congrArg (fun f => Quot (UnionRel (f := f) (A := A))) p.2.symm) p.1.2.2)
  left_inv ξ := F.baseChangeDownQ_baseChangeUp g A ξ
  right_inv p := Subtype.ext (Prod.ext rfl
    (F.baseChangeUp_baseChangeDownQ_cast g A p.1.1.down p.1.2 p.2))

/-- The comparison `F' ⟹ h_{S'} ×_{h_S} F`, assembled from the bijections
`...RelativeProjQcohSheaf.F.baseFibreEquiv` on the test schemes. -/
def F.baseChangeFibreNat : F.functor (baseAlgebra g A) ⟶ F.baseFibre g A where
  app T := TypeCat.ofHom (F.baseFibreEquiv g A T.unop)
  naturality _ _ φ := TypeCat.homEquiv.injective (funext fun ξ =>
    Subtype.ext (Prod.ext rfl (F.baseChangeUp_pullback g A φ.unop ξ)))

/-- The comparison is an isomorphism, its components being bijections. -/
instance F.isIso_baseChangeFibreNat : IsIso (F.baseChangeFibreNat g A) := by
  have : ∀ T : Scheme.{u}ᵒᵖ, IsIso ((F.baseChangeFibreNat g A).app T) := fun T =>
    (isIso_iff_bijective _).mpr (F.baseFibreEquiv g A T.unop).bijective
  exact NatIso.isIso_of_isIso_app _

/-- The comparison is compatible with the projection to the functor of points of the new base. -/
theorem F.baseChangeFibreNat_comp_fst :
    F.baseChangeFibreNat g A ≫ F.baseFibreFst g A = F.toBase (baseAlgebra g A) :=
  natTrans_ext_of_apply_eq fun _ _ => rfl

/-- The comparison is compatible with the projection to `F`. -/
theorem F.baseChangeFibreNat_comp_snd :
    F.baseChangeFibreNat g A ≫ F.baseFibreSnd g A = F.baseChangeNat g A :=
  natTrans_ext_of_apply_eq fun _ _ => rfl

/-- The comparison `F' ≅ h_{S'} ×_{h_S} F`, at the explicit fibre product
`...RelativeProjQcohSheaf.F.baseFibre`. -/
def F.baseChangeFibreIso : F.functor (baseAlgebra g A) ≅ F.baseFibre g A :=
  asIso (F.baseChangeFibreNat g A)

/-- **The analogue of Tag 01NT for the union `F` of the display 01NX.** *Let `g : S' ⟶ S` be a
morphism of schemes, set `𝒜' = g^*𝒜`, and let `F`, `F'` be the functors of the display 01NX
associated to `(S, 𝒜)` and `(S', 𝒜')`. Then there is a canonical isomorphism
`F' ≅ h_{S'} ×_{h_S} F` of functors.*

This is the statement the note on
`...RelativeProjQcohSheaf.Fd.isLimitBaseChangeCone` records as not proved: Tag 01NT itself is
about `F_d` at a fixed degree `d`, and the union over `d ≥ 1` is a different functor, on which
the comparison has to match the identification of Tag 01NW across degrees as well as strict
equivalence inside one degree.

As at fixed degree, the isomorphism is produced in its universal form: `F'`, together with its
projection `...RelativeProjQcohSheaf.F.toBase` to the functor of points of `S'` and the canonical
map `...RelativeProjQcohSheaf.F.baseChangeNat` to `F`, **is a limit of the cospan
`h_{S'} ⟶ h_S ⟵ F`**.  So the comparison is the canonical one, and
`...RelativeProjQcohSheaf.F.baseChangePullbackIso` reads it off as an isomorphism with the
categorical fibre product.

No hypothesis on `g`, on the degrees, or on the test scheme. -/
def F.isLimitBaseChangeCone :
    IsLimit (PullbackCone.mk (F.toBase (baseAlgebra g A)) (F.baseChangeNat g A)
      (F.toBase_comp_yonedaBaseMap g A)) :=
  IsLimit.ofIsoLimit (F.isLimitBaseFibre g A)
    (PullbackCone.ext (F.baseChangeFibreIso g A).symm
      ((IsIso.inv_hom_id_assoc (F.baseChangeFibreNat g A)
          (F.baseFibreFst g A)).symm.trans
        (congrArg (fun z => inv (F.baseChangeFibreNat g A) ≫ z)
          (F.baseChangeFibreNat_comp_fst g A)))
      ((IsIso.inv_hom_id_assoc (F.baseChangeFibreNat g A)
          (F.baseFibreSnd g A)).symm.trans
        (congrArg (fun z => inv (F.baseChangeFibreNat g A) ≫ z)
          (F.baseChangeFibreNat_comp_snd g A))))

/-- **The canonical isomorphism `F' ≅ h_{S'} ×_{h_S} F` for the union of the display 01NX**, with
the right-hand side the categorical fibre product of the cospan `h_{S'} ⟶ h_S ⟵ F` in the functor
category.  It is canonical: `...RelativeProjQcohSheaf.F.baseChangePullbackIso_hom_fst` and
`..._hom_snd` identify its composites with the two projections as the projection of `F'` to the
functor of points of `S'` and the canonical map `F' ⟹ F`. -/
def F.baseChangePullbackIso :
    F.functor (baseAlgebra g A) ≅ Limits.pullback (yonedaBaseMap g) (F.toBase A) :=
  IsLimit.conePointUniqueUpToIso (F.isLimitBaseChangeCone g A) (limit.isLimit _)

/-- The canonical isomorphism, followed by the projection to the functor of points of the new
base, is the projection of `F'` to that functor of points. -/
theorem F.baseChangePullbackIso_hom_fst :
    (F.baseChangePullbackIso g A).hom ≫ Limits.pullback.fst (yonedaBaseMap g) (F.toBase A) =
      F.toBase (baseAlgebra g A) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (F.isLimitBaseChangeCone g A)
    (limit.isLimit _) WalkingCospan.left

/-- The canonical isomorphism, followed by the projection to `F`, is the canonical map
`F' ⟹ F`. -/
theorem F.baseChangePullbackIso_hom_snd :
    (F.baseChangePullbackIso g A).hom ≫ Limits.pullback.snd (yonedaBaseMap g) (F.toBase A) =
      F.baseChangeNat g A :=
  IsLimit.conePointUniqueUpToIso_hom_comp (F.isLimitBaseChangeCone g A)
    (limit.isLimit _) WalkingCospan.right

end FLevel

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
