module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionAssociativity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomSiteEquivalence

/-!
# Composition of internal Hom complexes is invariant under an equivalence of ringed sites

Let `(C, O_C)` and `(D, O_D)` be ringed sites, let `e : C ≌ D` be an equivalence of the
underlying sites, continuous in both directions, and let `φ`, `ψ` be structure maps exhibiting
the two pushforwards of sheaves of modules as mutually inverse equivalences — the data of
`AlgebraicGeometry.RingedSite.siteEquivSheafHomComplexIso`. That transport carries the internal
Hom complex of two complexes to the internal Hom complex of their transports; this file proves
that it carries the composition morphism of [Stacks, Tag 0A91] to the composition morphism, and
the identity section to the identity section.

The statements are the ones of
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/CompositionSliceRestriction.lean` with
an arbitrary equivalence of ringed sites in place of restriction to a slice site. As there, the
composition of local sections is the whole content of
`AlgebraicGeometry.RingedSite.compositionMap`, so the statement is the compatibility of
`AlgebraicGeometry.RingedSite.compositionSection` with the transport, free of any comparison of
the two total tensor products involved.

## Main results

* `AlgebraicGeometry.RingedSite.applyHomSectionOver_siteEquivSheafHomComplexIso`: the transport
  does not change the value of a local section of an internal Hom complex on a local section of
  its source — evaluating the transported section over an object `W` of `C` is evaluating the
  original over `e(W)`.
* `AlgebraicGeometry.RingedSite.compositionSection_siteEquivSheafHomComplexIso`: **the transport
  carries composition to composition.**
* `AlgebraicGeometry.RingedSite.idSection_siteEquivSheafHomComplexIso`: the transport carries
  the identity section to the identity section.

## Implementation notes

The proof is the evaluation principle and nothing else, exactly as for restriction to a slice:
a section of an internal Hom complex is determined by its values
(`AlgebraicGeometry.RingedSite.homSection_ext`), the value of a composite is the two values in
turn with no sign (`AlgebraicGeometry.RingedSite.compositionSection_applyOver`), and the value
of a transported section is the value of the original, which is
`AlgebraicGeometry.RingedSite.siteEquivSectionIso_apply_section`. The two evaluations are taken
over `W` on one site and over `e(W)` on the other, and the arrow they are taken along is `i` on
one side and `e(i)` on the other.

Sections of `φ_* A` over `W` are sections of `A` over `e(W)`, and the two are the same only
after the pushforward of presheaves of modules and its restriction of scalars are unfolded; the
functors involved are made `implicit_reducible` locally, as in
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/SheafHomSiteEquivalence.lean`.

## References

* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

variable {X Y : RingedSite.{u, u, u}} (eqv : Y.C ≌ X.C)
  [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{u} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (eqv.inverse.sheafPushforwardContinuous RingCat.{u} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)

/-- **An equivalence of ringed sites does not change the value of a local section of an internal
Hom complex.** For objects `V`, `W` of `C` with an arrow `i : W ⟶ V`, a degree-`n` section `s`
of `SheafHom(A, B)` over `e(V)` and a degree-`p` section `x` of `A` over `e(W)`, evaluating the
transported section on `x` along `i` gives the same section of `B` as evaluating `s` on `x`
along `e(i)`. -/
theorem applyHomSectionOver_siteEquivSheafHomComplexIso
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (V W : Y.C) (i : W ⟶ V) (n p q : ℤ) (hpq : p + n = q)
    (s : ((sheafHomComplex X A B).obj.X n).val.obj (op (eqv.functor.obj V)))
    (x : (A.X p).val.obj (op (eqv.functor.obj W))) :
    applyHomSectionOver Y
        (sheafHomComplex Y ((pushComplex eqv φ).obj A) ((pushComplex eqv φ).obj B))
        V W i n p q hpq
        (((siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ A B).hom.f n).val.app (op V) s) x =
      applyHomSectionOver X (sheafHomComplex X A B) (eqv.functor.obj V) (eqv.functor.obj W)
        (eqv.functor.map i) n p q hpq s x :=
  siteEquivSectionIso_apply_section eqv φ ψ H₁ H₂ A B V n p q hpq s i x

/-- **An equivalence of ringed sites carries the composition of local sections of internal Hom
complexes to the composition of their transports.** This is the compatibility of the composition
morphism of [Stacks, Tag 0A91] with the transport, read on the homogeneous local sections which
characterise that morphism: for a degree-`p` section `β` of `SheafHom(L, M)` and a degree-`q`
section `γ` of `SheafHom(K, L)` over `e(V)`,

`φ_*(β ∘ γ) = φ_* β ∘ φ_* γ`. -/
theorem compositionSection_siteEquivSheafHomComplexIso
    (K L M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (V : Y.C) (p q n : ℤ) (hn : p + q = n)
    (β : ((sheafHomComplex X L M).obj.X p).val.obj (op (eqv.functor.obj V)))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op (eqv.functor.obj V))) :
    (((siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ K M).hom.f n).val.app (op V)
        (compositionSection X (eqv.functor.obj V) p q n hn β γ)) =
      compositionSection Y V p q n hn
        (((siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ L M).hom.f p).val.app (op V) β)
        (((siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ K L).hom.f q).val.app (op V) γ) := by
  refine homSection_ext Y
    (sheafHomComplex Y ((pushComplex eqv φ).obj K) ((pushComplex eqv φ).obj M))
    V n fun r t hrt W i x ↦ ?_
  rw [applyHomSectionOver_siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ K M V W i n r t hrt
      (compositionSection X (eqv.functor.obj V) p q n hn β γ) x,
    compositionSection_applyOver X (eqv.functor.obj V) (eqv.functor.obj W) (eqv.functor.map i)
      p q n r (r + q) t hn rfl (by omega) β γ x,
    compositionSection_applyOver Y V W i p q n r (r + q) t hn rfl (by omega)
      (((siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ L M).hom.f p).val.app (op V) β)
      (((siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ K L).hom.f q).val.app (op V) γ) x,
    applyHomSectionOver_siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ K L V W i q r (r + q) rfl γ x,
    applyHomSectionOver_siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ L M V W i p (r + q) t
      (by omega) β _]

/-- **An equivalence of ringed sites carries the identity section to the identity section.** The
identity section of `SheafHom(P, P)` is characterised by its values
(`AlgebraicGeometry.RingedSite.applyHomSectionOver_idSection`), and the transport does not
change the value of a section; so the two sides have the same values. -/
theorem idSection_siteEquivSheafHomComplexIso
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (V : Y.C) :
    ((siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ P P).hom.f 0).val.app (op V)
        (idSection X P (eqv.functor.obj V)) =
      idSection Y ((pushComplex eqv φ).obj P) V := by
  refine homSection_ext Y
    (sheafHomComplex Y ((pushComplex eqv φ).obj P) ((pushComplex eqv φ).obj P))
    V 0 fun r t hrt W i x ↦ ?_
  obtain rfl : t = r := by omega
  refine (applyHomSectionOver_siteEquivSheafHomComplexIso eqv φ ψ H₁ H₂ P P V W i 0 t t hrt
    (idSection X P (eqv.functor.obj V)) x).trans ?_
  exact (applyHomSectionOver_idSection X P (eqv.functor.obj V) (eqv.functor.obj W)
      (eqv.functor.map i) t x).trans
    (applyHomSectionOver_idSection Y ((pushComplex eqv φ).obj P) V W i t x).symm

end AlgebraicGeometry.RingedSite

end
