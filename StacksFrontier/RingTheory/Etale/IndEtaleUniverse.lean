module

public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite

/-!
# Ind-étale algebras with the base and the algebra in independent universes

`(CommAlgCat.etale R).ind (CommAlgCat.of R B)` requires `R` and `B` to live in one universe,
because the category `CommAlgCat.{w} R` only contains `R`-algebras of size `w`. This file
introduces the lifted form

`StacksDraft.IndEtale A B := (CommAlgCat.etale.{max u v} A).ind (CommAlgCat.of A (ULift.{u} B))`

for `A : Type u` and `B : Type v`, which is exactly the shape of the `ind_etale` field of
`IsLocalRing.IsHenselization`, and proves for it the closure properties that
`StacksFrontier.RingTheory.Etale.FilteredColimit.Basic` proves in a single universe.

## Main definitions

* `StacksDraft.IndEtale`: `B` is a filtered colimit of étale `A`-algebras, with `A` and `B` in
  independent universes.

## Main results

* `StacksDraft.indEtale_iff`: in a common universe the lifted form is the unlifted one.
* `StacksDraft.indEtale_of_directed_etale_subalgebras`: a directed family of étale subalgebras
  whose supremum is the whole algebra exhibits it as ind-étale.
* `StacksDraft.indEtale_of_equiv`: transport along a commuting square of ring equivalences, which
  may change every universe involved.
* `StacksDraft.indEtale_comp`, `StacksDraft.indEtale_of_comp`: Lemmas 0BSI and 08HS across
  universes.
* `StacksDraft.indEtale_atPrime`: a localization at a prime is ind-étale (Lemma 00QP), across
  universes.
* `StacksDraft.indEtale_tensorProduct`: cobase change (Lemma 0BSH) across universes, in the
  tensor-product model.

## Implementation notes

The universe-changing step is `StacksDraft.indEtale_ofEquivAux`, which rewrites ind-étaleness into
the factorization criterion of Lemma 07C3: "every `A`-algebra map from a finitely presented
`A`-algebra `C` into `B` factors through an étale `A`-algebra". That criterion is stable under
changing the universe because a finitely presented algebra, and an étale algebra, can be shrunk
into the universe of the base (`Algebra.FiniteType.small`). Once the universes can be changed at
will, every closure property is obtained by lifting the three rings involved into a common
universe with `ULift`, applying the single-universe lemma of
`StacksFrontier.RingTheory.Etale.FilteredColimit.Basic`, and coming back.

The base change of the ambient category along a ring equivalence is
`StacksDraft.commAlgChangeScalarsEquivalence`; only the equivalence of categories is needed, not
functoriality of the whole construction, so it is kept private.

## References

* [StacksProject 0BSI](https://stacks.math.columbia.edu/tag/0BSI)
* [StacksProject 08HS](https://stacks.math.columbia.edu/tag/08HS)
* [StacksProject 0BSH](https://stacks.math.columbia.edu/tag/0BSH)
* [StacksProject 07C3](https://stacks.math.columbia.edu/tag/07C3)

## Tags

ind-étale, étale algebra, filtered colimit, universe, ULift
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w

namespace StacksDraft

/-- Étale ring maps compose. This is `Algebra.Etale.comp` for ring maps between rings in
independent universes, which is what the universe-changing arguments below need. -/
public theorem etale_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (hf : f.Etale) (hg : g.Etale) : (g.comp f).Etale := by
  algebraize [f, g, g.comp f]
  exact Algebra.Etale.comp R S T

/-- Ind-étaleness in the form of the factorization criterion of Lemma 07C3: every map into `B`
from a finitely presented `A`-algebra factors through an étale `A`-algebra. Unlike
`(CommAlgCat.etale A).ind`, this form does not mention the ambient category, which is what makes
it possible to change the universe. -/
private theorem ind_etale_iff_factorization {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B] :
    (CommAlgCat.etale A).ind.{u} (CommAlgCat.of A B) ↔
      ∀ (C : Type u) [CommRing C] [Algebra A C] [Algebra.FinitePresentation A C]
        (f : C →ₐ[A] B), ∃ (E : Type u) (_ : CommRing E) (_ : Algebra A E),
          Algebra.Etale A E ∧ ∃ (g : C →ₐ[A] E) (h : E →ₐ[A] B), h.comp g = f := by
  rw [CommAlgCat.ind_etale_iff_ind_algebraMap, MorphismProperty.ind_iff_ind_underMk,
    CommRingCat.ind_under_iff_exists_factorization _
      (fun (C : Under (CommRingCat.of A)) (h : CommRingCat.etale.underObj C) =>
        (RingHom.Etale.iff_flat_and_formallyUnramified.mp h).2.2)]
  constructor
  · intro H C _ _ _ f
    obtain ⟨E, g, h, he, het⟩ := H
      (Under.mk (CommRingCat.ofHom (algebraMap A C)))
      (show (algebraMap A C).FinitePresentation from
        RingHom.finitePresentation_algebraMap.mpr inferInstance)
      (Under.homMk (CommRingCat.ofHom f.toRingHom) (by ext x; exact f.commutes x))
    let := E.hom.hom.toAlgebra
    refine ⟨E.right, inferInstance, inferInstance, RingHom.etale_algebraMap.mp het,
      ⟨g.right.hom, fun x => congr($(Under.w g).hom x)⟩,
      ⟨h.right.hom, fun x => congr($(Under.w h).hom x)⟩, ?_⟩
    ext x
    exact congr($(congrArg Under.Hom.right he).hom x)
  · intro H C hC f
    let := C.hom.hom.toAlgebra
    let : Algebra.FinitePresentation A C.right := RingHom.finitePresentation_algebraMap.mp hC
    obtain ⟨E, _, _, het, g, h, he⟩ := H C.right
      ⟨f.right.hom, fun x => congr($(Under.w f).hom x)⟩
    refine ⟨Under.mk (CommRingCat.ofHom (algebraMap A E)),
      Under.homMk (CommRingCat.ofHom g.toRingHom) (by ext x; exact g.commutes x),
      Under.homMk (CommRingCat.ofHom h.toRingHom) (by ext x; exact h.commutes x),
      ?_, show RingHom.Etale (algebraMap A E) from RingHom.etale_algebraMap.mpr het⟩
    ext x
    exact AlgHom.congr_fun he x

/-- Ind-étaleness transports along a commuting square of ring equivalences, even when the two
sides live in different universes: the factorization criterion is checked after shrinking the
finitely presented test algebra, respectively the étale algebra it factors through, into the
universe of the base. -/
private theorem indEtale_ofEquivAux {A B : Type u} {A' B' : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    [CommRing A'] [CommRing B'] [Algebra A' B']
    (eA : A ≃+* A') (eB : B ≃+* B')
    (he : ∀ a, eB (algebraMap A B a) = algebraMap A' B' (eA a))
    (hi : (CommAlgCat.etale A).ind.{u} (CommAlgCat.of A B)) :
    (CommAlgCat.etale A').ind.{v} (CommAlgCat.of A' B') := by
  classical
  rw [ind_etale_iff_factorization] at hi ⊢
  intro C _ _ _ f
  let : Algebra A C := ((algebraMap A' C).comp eA.toRingHom).toAlgebra
  have hfp : Algebra.FinitePresentation A C :=
    RingHom.finitePresentation_algebraMap.mp <| RingHom.FinitePresentation.comp
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
      (RingHom.FinitePresentation.of_bijective eA.bijective)
  let : Small.{u} C := Algebra.FiniteType.small (R := A) (S := C)
  let eC : Shrink.{u} C ≃ₐ[A] C := Shrink.algEquiv A C
  let f' : Shrink.{u} C →ₐ[A] B :=
    { toRingHom := eB.symm.toRingHom.comp (f.toRingHom.comp eC.toRingEquiv.toRingHom)
      commutes' := by
        intro a
        change eB.symm (f (eC (algebraMap A (Shrink C) a))) = _
        rw [eC.commutes]
        change eB.symm (f (algebraMap A' C (eA a))) = _
        rw [f.commutes, ← he, eB.symm_apply_apply] }
  let : Algebra.FinitePresentation A (Shrink.{u} C) :=
    Algebra.FinitePresentation.equiv eC.symm
  obtain ⟨E, _, _, het, g, h, hgh⟩ := hi _ f'
  let : Algebra A' E := ((algebraMap A E).comp eA.symm.toRingHom).toAlgebra
  have het' : Algebra.Etale A' E := RingHom.etale_algebraMap.mp <|
    etale_comp eA.symm.toRingHom (algebraMap A E)
      (RingHom.Etale.of_bijective eA.symm.bijective) (RingHom.etale_algebraMap.mpr het)
  let : Small.{v} E := Algebra.FiniteType.small (R := A') (S := E)
  let eE : Shrink.{v} E ≃ₐ[A'] E := Shrink.algEquiv A' E
  have hetE : Algebra.Etale A' (Shrink.{v} E) := Algebra.Etale.of_equiv eE.symm
  refine ⟨Shrink.{v} E, inferInstance, inferInstance, hetE,
    { toRingHom := eE.symm.toRingEquiv.toRingHom.comp
        (g.toRingHom.comp eC.symm.toRingEquiv.toRingHom)
      commutes' := ?_ },
    { toRingHom := eB.toRingHom.comp (h.toRingHom.comp eE.toRingEquiv.toRingHom)
      commutes' := ?_ }, ?_⟩
  · intro a
    have hc : algebraMap A' C a = algebraMap A C (eA.symm a) :=
      (congrArg (algebraMap A' C) (eA.apply_symm_apply a)).symm
    apply eE.injective
    change eE (eE.symm (g (eC.symm (algebraMap A' C a)))) = _
    rw [eE.apply_symm_apply, eE.commutes, hc, eC.symm.commutes, g.commutes]
    rfl
  · intro a
    change eB (h (eE (algebraMap A' (Shrink E) a))) = _
    rw [eE.commutes]
    change eB (h (algebraMap A E (eA.symm a))) = _
    rw [h.commutes, he, eA.apply_symm_apply]
  · ext c
    change eB (h (eE (eE.symm (g (eC.symm c))))) = f c
    rw [eE.apply_symm_apply, ← AlgHom.comp_apply, hgh]
    change eB (eB.symm (f (eC (eC.symm c)))) = f c
    rw [eC.apply_symm_apply, eB.apply_symm_apply]

/-- Restriction of scalars along a ring equivalence, on categories of commutative algebras. -/
public def commAlgChangeScalars {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (e : A ≃+* B) : CommAlgCat.{w} A ⥤ CommAlgCat.{w} B where
  obj C := let := ((algebraMap A C).comp e.symm.toRingHom).toAlgebra
           CommAlgCat.of B C
  map {C D} f := by
    let := ((algebraMap A C).comp e.symm.toRingHom).toAlgebra
    let := ((algebraMap A D).comp e.symm.toRingHom).toAlgebra
    exact CommAlgCat.ofHom
      { f.hom.toRingHom with commutes' := fun b => f.hom.commutes (e.symm b) }

/-- A ring equivalence of bases induces an equivalence of the algebra categories. -/
public def commAlgChangeScalarsEquivalence {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (e : A ≃+* B) : CommAlgCat.{w} A ≌ CommAlgCat.{w} B where
  functor := commAlgChangeScalars e
  inverse := commAlgChangeScalars e.symm
  unitIso := NatIso.ofComponents (fun C =>
    @CommAlgCat.isoMk A _ C
      ((commAlgChangeScalars e.symm).obj ((commAlgChangeScalars e).obj C))
      C.commRing _ C.algebra
      (((commAlgChangeScalars e.symm).obj ((commAlgChangeScalars e).obj C)).algebra)
      { toRingEquiv := RingEquiv.refl C
        commutes' := by
          intro a
          change algebraMap A C a = algebraMap A C (e.symm (e a))
          rw [e.symm_apply_apply] })
  counitIso := NatIso.ofComponents (fun C =>
    @CommAlgCat.isoMk B _
      ((commAlgChangeScalars e).obj ((commAlgChangeScalars e.symm).obj C)) C
      _ C.commRing (((commAlgChangeScalars e).obj ((commAlgChangeScalars e.symm).obj C)).algebra)
      C.algebra
      { toRingEquiv := RingEquiv.refl C
        commutes' := by
          intro b
          change algebraMap B C (e (e.symm b)) = algebraMap B C b
          rw [e.apply_symm_apply] })

/-- Ind-étaleness of a fixed algebra is invariant under a ring equivalence of the base, the
universe of the algebra being untouched. -/
private theorem ind_etale_changeScalars {A : Type u} {B : Type v} {T : Type w}
    [CommRing A] [CommRing B] [CommRing T] [Algebra A T] [Algebra B T]
    (e : A ≃+* B) (he : ∀ a, algebraMap A T a = algebraMap B T (e a))
    (hi : (CommAlgCat.etale A).ind.{w} (CommAlgCat.of A T)) :
    (CommAlgCat.etale B).ind.{w} (CommAlgCat.of B T) := by
  obtain ⟨J, _, _, pres, hp⟩ := hi
  let E := commAlgChangeScalarsEquivalence.{u, v, w} e
  have ht : (CommAlgCat.etale B).ind.{w} (E.functor.obj (CommAlgCat.of A T)) := by
    refine ⟨J, inferInstance, inferInstance, pres.map E.functor, fun j => ?_⟩
    apply RingHom.etale_algebraMap.mp
    exact etale_comp e.symm.toRingHom (algebraMap A (pres.diag.obj j))
      (RingHom.Etale.of_bijective e.symm.bijective) (RingHom.etale_algebraMap.mpr (hp j))
  refine (CommAlgCat.etale B).ind.prop_of_iso ?_ ht
  exact @CommAlgCat.isoMk B _ (E.functor.obj (CommAlgCat.of A T)) T
    _ _ (E.functor.obj (CommAlgCat.of A T)).algebra _
    { toRingEquiv := RingEquiv.refl T
      commutes' := by
        intro b
        change algebraMap A T (e.symm b) = algebraMap B T b
        rw [he, e.apply_symm_apply] }

/-- **Ind-étaleness with the base and the algebra in independent universes.** For `A : Type u` and
`B : Type v`, the `A`-algebra `B` is *ind-étale* if `ULift.{u} B` is a filtered colimit of étale
`A`-algebras in `CommAlgCat.{max u v} A`. This is the shape of the `ind_etale` field of
`IsLocalRing.IsHenselization`, and in a common universe it is the usual condition
(`StacksDraft.indEtale_iff`). -/
@[stacks 097I]
abbrev IndEtale (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] : Prop :=
  (CommAlgCat.etale.{max u v} A).ind.{max u v} (CommAlgCat.of A (ULift.{u} B))

/-- Ind-étaleness of `A → B` is ind-étaleness of the fully lifted map `ULift A → ULift B`, which
lives in a single universe. -/
private theorem indEtale_iff_lift {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] :
    IndEtale A B ↔
      let : Algebra (ULift.{v} A) (ULift.{u} B) := ULift.algebra' A _
      (CommAlgCat.etale (ULift.{v} A)).ind.{max u v}
        (CommAlgCat.of (ULift.{v} A) (ULift.{u} B)) := by
  let : Algebra (ULift.{v} A) (ULift.{u} B) := ULift.algebra' A _
  exact ⟨ind_etale_changeScalars ULift.ringEquiv.symm (fun _ => rfl),
    ind_etale_changeScalars ULift.ringEquiv (fun _ => rfl)⟩

attribute [local instance] ULift.algebra' in
/-- **Ind-étaleness transports along a commuting square of ring equivalences**, with all four
universes independent. -/
theorem indEtale_of_equiv {A B A' B' : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    [CommRing A'] [CommRing B'] [Algebra A' B']
    (eA : A ≃+* A') (eB : B ≃+* B')
    (he : ∀ a, eB (algebraMap A B a) = algebraMap A' B' (eA a))
    (hi : IndEtale A B) : IndEtale A' B' := by
  rw [indEtale_iff_lift] at hi ⊢
  exact indEtale_ofEquivAux
    (ULift.ringEquiv.trans (eA.trans ULift.ringEquiv.symm))
    (ULift.ringEquiv.trans (eB.trans ULift.ringEquiv.symm))
    (fun a => ULift.ext (he a.down)) hi

/-- In a common universe the lifted condition is the unlifted one. -/
theorem indEtale_iff {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
    IndEtale A B ↔ (CommAlgCat.etale A).ind.{u} (CommAlgCat.of A B) :=
  ⟨(CommAlgCat.etale A).ind.prop_of_iso (CommAlgCat.isoMk ULift.algEquiv),
    (CommAlgCat.etale A).ind.prop_of_iso (CommAlgCat.isoMk ULift.algEquiv.symm)⟩

/-- **A directed union of étale subalgebras is ind-étale.** If the `A`-algebra `B` is the
supremum of a directed family `S` of `A`-subalgebras, each of which is étale over `A`, then `B`
is ind-étale over `A`.

This is the concrete, subalgebra-shaped form of Definition 04GQ: it turns a directed family
covering `B` into the categorical statement that `B` is a filtered colimit of étale
`A`-algebras. A finitely presented `A`-algebra mapping to `B` has finitely many generators,
whose images all lie in a single member of the family by directedness, so the map factors
through that member; this is the factorization criterion of Lemma 07C3. -/
theorem indEtale_of_directed_etale_subalgebras {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] {ι : Type*} [Nonempty ι] (S : ι → Subalgebra A B)
    (hdir : Directed (· ≤ ·) S) (het : ∀ i, Algebra.Etale A (S i)) (hsup : iSup S = ⊤) :
    IndEtale A B := by
  classical
  have hmem : ∀ b : B, ∃ i, b ∈ S i := by
    intro b
    have hb : b ∈ iSup S := by rw [hsup]; trivial
    rwa [← SetLike.mem_coe, Subalgebra.coe_iSup_of_directed hdir, Set.mem_iUnion] at hb
  choose index hindex using hmem
  rw [indEtale_iff, ind_etale_iff_factorization]
  intro C _ _ _ f
  obtain ⟨gens, hgens⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra A C).FG)
  obtain ⟨i, hi⟩ := hdir.finset_le (gens.image fun c => index (f c))
  have hrange : (⊤ : Subalgebra A C).map f ≤ S i := by
    rw [← hgens, AlgHom.map_adjoin]
    refine Algebra.adjoin_le ?_
    rintro b ⟨c, hc, rfl⟩
    exact hi _ (Finset.mem_image_of_mem _ hc) (hindex (f c))
  refine ⟨S i, inferInstance, inferInstance, het i,
    f.codRestrict (S i) fun c => hrange ⟨c, Algebra.mem_top, rfl⟩, (S i).val,
    AlgHom.ext fun _ => rfl⟩

/-- Ind-étaleness is invariant under lifting the base and the algebra to larger universes. -/
private theorem indEtale_uLift.{a, b} {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] (hB : IndEtale A B) :
    let : Algebra (ULift.{a} A) (ULift.{b} B) := ULift.algebra' A _
    IndEtale (ULift.{a} A) (ULift.{b} B) := by
  intro _
  exact indEtale_of_equiv ULift.ringEquiv.symm ULift.ringEquiv.symm (fun _ => rfl) hB

attribute [local instance] ULift.algebra' in
/-- **Lemma 0BSI across universes.** If `B` is ind-étale over `A` and `C` is ind-étale over `B`,
then `C` is ind-étale over `A`. -/
@[stacks 0BSI "\"`A → B` is a filtered colimit of étale ring maps\" is `StacksDraft.IndEtale A B`
(Lemma `097I`), with `A`, `B` and `C` in independent universes, and the source's `A → B → C` is an
`IsScalarTower A B C`. The single-universe form is `CommAlgCat.ind_etale_comp`."]
theorem indEtale_comp {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hB : IndEtale A B) (hC : IndEtale B C) : IndEtale A C := by
  have hb : IndEtale (ULift.{max v w} A) (ULift.{max u w} B) := indEtale_uLift hB
  have hc : IndEtale (ULift.{max u w} B) (ULift.{max u v} C) := indEtale_uLift hC
  have hac : IndEtale (ULift.{max v w} A) (ULift.{max u v} C) := indEtale_iff.mpr
    (CommAlgCat.ind_etale_comp (indEtale_iff.mp hb) (indEtale_iff.mp hc))
  exact indEtale_of_equiv ULift.ringEquiv ULift.ringEquiv (fun _ => rfl) hac

attribute [local instance] ULift.algebra' in
/-- **Lemma 08HS across universes.** If `B` and `C` are both ind-étale over `A`, then `C` is
ind-étale over `B`. -/
theorem indEtale_of_comp {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (hB : IndEtale A B) (hC : IndEtale A C) : IndEtale B C := by
  have hb : IndEtale (ULift.{max v w} A) (ULift.{max u w} B) := indEtale_uLift hB
  have hc : IndEtale (ULift.{max v w} A) (ULift.{max u v} C) := indEtale_uLift hC
  have hbc : IndEtale (ULift.{max u w} B) (ULift.{max u v} C) := indEtale_iff.mpr
    (CommAlgCat.ind_etale_of_comp (indEtale_iff.mp hb) (indEtale_iff.mp hc))
  exact indEtale_of_equiv ULift.ringEquiv ULift.ringEquiv (fun _ => rfl) hbc

/-- **A localization at a prime is ind-étale**, with the localization in any universe. -/
theorem indEtale_atPrime {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime B p] : IndEtale A B :=
  indEtale_of_equiv (RingEquiv.refl A)
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) B).toRingEquiv
    (fun a => (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) B).commutes a)
    (indEtale_iff.mpr (CommAlgCat.ind_etale_atPrime A (Localization.AtPrime p) p))

/-- **Lemma 0BSH across universes**, in the tensor-product model: if `B` is ind-étale over `A`,
then `S ⊗[A] B` is ind-étale over `S`, for any `A`-algebra `S`. -/
theorem indEtale_tensorProduct {A : Type u} {B : Type v} (S : Type w)
    [CommRing A] [CommRing B] [CommRing S] [Algebra A B] [Algebra A S]
    (hi : IndEtale A B) : IndEtale S (S ⊗[A] B) := by
  let A' := ULift.{max v w} A
  let B' := ULift.{max u w} B
  let S' := ULift.{max u v} S
  let : Algebra A' B' := ULift.algebra' A _
  let : Algebra A' S' := ULift.algebra' A _
  have hb : IndEtale A' B' := indEtale_uLift hi
  let : Algebra B' (S' ⊗[A'] B') := Algebra.TensorProduct.rightAlgebra
  let := Algebra.TensorProduct.right_isScalarTower (R := A') (A := S') (B := B')
  have ht : IndEtale S' (S' ⊗[A'] B') := indEtale_iff.mpr
    (CommAlgCat.ind_etale_of_isPushout A' S' B' (S' ⊗[A'] B') (indEtale_iff.mp hb))
  let e : S' ⊗[A'] B' ≃+* S ⊗[A] B :=
    (Algebra.TensorProduct.equivOfCompatibleSMul A A' S' S' B').toRingEquiv.trans
      (Algebra.TensorProduct.congr
        (ULift.algEquiv : S' ≃ₐ[A] S) (ULift.algEquiv : B' ≃ₐ[A] B)).toRingEquiv
  exact indEtale_of_equiv ULift.ringEquiv e (fun _ => rfl) ht

end StacksDraft

end
