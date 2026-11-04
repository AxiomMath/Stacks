module

public import StacksFrontier.Algebra.Category.CommAlgCat.FilteredColimits
public import StacksFrontier.RingTheory.Henselian.Henselization.Existence
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Existence
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Unramified.Finite
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v w



/-!
# The henselization and the strict henselization of a local ring

Let `(R, 𝔪, κ)` be a local ring and let `κ ⊆ L` be an extension of its residue field. A
*henselization of `R` with residue field `L`* is a local `R`-algebra `Rh` which is henselian, is a
filtered colimit of étale `R`-algebras, and whose residue field is `L` compatibly with `κ ⊆ L`.

Lemma 04GN produces such an `Rh` for `L = κ`, and that local ring map `R → R^h` is *the
henselization* of `R`; Lemma 04GP produces one for `L = κ^sep` a separable algebraic closure of
`κ`, and that local ring map `R → R^{sh}` is *the strict henselization of `R` with respect to
`κ ⊆ κ^sep`*. By Lemma 08HT a henselization with residue field `L` is unique up to a unique
`R`-algebra isomorphism over `L`, so the definite article is legitimate, and a local ring map
`R → R^{sh}` is isomorphic to one of the maps constructed in Lemma 04GP exactly when it satisfies
the three conditions above with `L = κ^sep`, since each of them is invariant under isomorphism.
That is how the source's three items are read here: they are the two instances `L = κ` and
`L = κ^sep` of one predicate, and its isomorphism invariance.

## Main definitions

* `IsLocalRing.IsHenselization R L Rh`: the local `R`-algebra `Rh` is a henselization of the local
  ring `R` with residue field the given extension `κ ⊆ L` of the residue field of `R`. For `L = κ`
  this is the henselization `R → R^h`, for `L = κ^sep` a strict henselization `R → R^{sh}`.
* `Stacks.Henselization.Shared.commAlgCatRestrictScalars`: restriction of scalars
  `CommAlgCat S ⥤ CommAlgCat R` along a ring equivalence `R ≃+* S`, and
  `Stacks.Henselization.Shared.commAlgCatRestrictScalarsEquivalence`, the induced equivalence of
  categories. These are the bookkeeping that lets a statement about `IsHenselization` be reduced to
  an equal-universe form by restricting scalars along `ULift.ringEquiv`, so they are needed by
  every development built on this predicate; they live here because this module is the only common
  ancestor of the import-incomparable modules that use them.

## Main results

* `IsLocalRing.IsHenselization.isLocalHom`: the structure map is local.
* `IsLocalRing.IsHenselization.flat`: a henselization is flat over its base ring.
* `IsLocalRing.IsHenselization.faithfullyFlat`: the structure map is faithfully flat.
* `IsLocalRing.IsHenselization.map_maximalIdeal`: its maximal ideal is extended from the base.
* `Stacks.Henselization.Shared.ind_etale_restrictScalars`: ind-étaleness is preserved by
  restriction of scalars along a ring equivalence. It accompanies the two definitions above for
  the same reason, and is stated here for the same reason.

## Implementation notes

*One predicate, two instantiations.* The source names the two maps its Lemmas 04GN and 04GP
construct, and then declares (item (3)) that anything isomorphic to the second is again called a
strict henselization. The generalization to an arbitrary extension `κ ⊆ L` is the one the source's
own uniqueness statement is phrased at: Lemma 08HT takes a field `K` and two henselian ind-étale
`R`-algebras surjecting onto it, and concludes that they are uniquely isomorphic over `K`. So the
predicate here is exactly the notion 08HT determines, and the henselization (`L = κ`) and the
strict henselizations (`L = κ^sep`) are its two named instances. For `L` neither `κ` nor a
separable algebraic closure of `κ` the intermediate cases are the finite étale local extensions
`R^h ⊆ R^h(κ')` of Remark 0BSL.

*Why a characterisation and not a reference to Lemma 04GP.* Item (3) says "isomorphic to one of
the local ring maps constructed in Lemma 04GP". That lemma is an existence statement, so "one of
the maps it constructs" is not a term one can name; what makes the phrase well defined is the
paragraph following the definition in the source, which records that the conditions of being
henselian local, a filtered colimit of étale `R`-algebras, and having residue field `κ^sep`
determine `R^{sh}` up to unique isomorphism (Lemma 08HT). Those conditions are the fields of this
class, so a local `R`-algebra satisfies it if and only if it is isomorphic over `R` to the ring
04GP constructs — the "if" because every field is invariant under isomorphism, the "only if" by
08HT. The same reading gives item (1) at `L = κ` via Lemma 04GN.

*A filtered colimit of étale `R`-algebras is an ind-étale `R`-algebra.* `ind_etale` is
`(CommAlgCat.etale R).ind (CommAlgCat.of R Rh)`, the spelling of item (2) of Lemma 04GN and item
(3) of Lemma 04GP: `CategoryTheory.ObjectProperty.ind P X` says that `X` is the colimit of a
filtered diagram all of whose values satisfy `P`, and the colimit is taken in `CommAlgCat R`, so
the diagram, the cocone and the structure map `R → Rh` are all over `R`. The base ring, residue
extension, and henselization have independent universes. Both the index category and the étale
stages are taken in `max u w`, where `R : Type u` and `Rh : Type w`. The colimit object is
`ULift.{u} Rh`, so neither
the base nor the henselization universe is constrained by the other.

*The residue field condition is `exists_residueFieldEquiv`, quantified existentially.* It is item
(5) of Lemma 04GP verbatim: an isomorphism `e : L ≃+* ResidueField Rh` with
`e (algebraMap κ L (residue R x)) = residue Rh (algebraMap R Rh x)` for all `x : R`, that is, the
commutative square `R → Rh`, `κ → L → ResidueField Rh`. Since `residue R` is surjective this says
that `e` restricted to `κ` is the residue field map of `R → Rh`, so it pins the extension `κ ⊆ L`
against the extension `κ ⊆ ResidueField Rh` and not merely the abstract fields. The isomorphism is
*not* part of the data: a `κ`-isomorphism `κ^sep ≃ ResidueField R^{sh}` is unique only up to the
Galois action, and the source's item (3) is itself a statement up to isomorphism. At `L = κ` the
condition is `Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R Rh))`, item (4) of
Lemma 04GN, since a ring map between fields is injective.

*Locality of `R → Rh` is not a condition.* The source's "local ring map `R → R^h`" is a
consequence of `exists_residueFieldEquiv`: the kernel of `residue Rh ∘ algebraMap R Rh` is the
preimage of `maximalIdeal Rh`, and by the displayed compatibility it equals the kernel of
`algebraMap κ L ∘ residue R`, which is `maximalIdeal R` because `κ → L` is injective. So
`IsLocalHom (algebraMap R Rh)` holds for every `Rh` satisfying this class, and carrying it as a
field would be carrying a consequence. This is exported by `IsHenselization.isLocalHom`.
Together with flatness of filtered colimits of étale algebras (`IsHenselization.flat`), it gives
`IsHenselization.faithfullyFlat`. These are theorems with an explicit `(L := L)` argument, since
the prescribed residue extension cannot be inferred from the flatness or locality conclusion.

*`𝔪 Rh = 𝔪_{Rh}` is not a condition either.* Item (3) of Lemma 04GN and item (4) of Lemma 04GP
state `(maximalIdeal R).map (algebraMap R Rh) = maximalIdeal Rh`; it is omitted here for the same
reason. For every local ind-étale algebra this follows by representing a maximal-ideal element
at an étale stage, then using the maximal-ideal equality for its localization at the contracted
prime. This is exported by `IsHenselization.map_maximalIdeal`. The three fields kept are precisely
the conditions the source's own uniqueness paragraph lists as determining `R^h` and `R^{sh}`.

Faithfulness to [StacksProject 04GQ], point by point. (1) No binder is dead: `R` local is used
through `residue R` and `ResidueField R`, the extension `κ ⊆ L` through `algebraMap κ L`, and the
`R`-algebra structure of `Rh` through `algebraMap R Rh` and `ind_etale`; a class has no hypothesis
that the conclusion could fail to use. (2) The scalars and the base are the source's: `Rh` is an
`R`-algebra, the filtered colimit is one of `R`-algebras (`CommAlgCat R`), and `L` is an extension
of the residue field of `R` itself, not of a localization or a quotient of `R`. (3) The maps the
source names are pinned: the local ring map is `algebraMap R Rh`, and the residue field condition
is the commutativity of the square built from `residue R`, `algebraMap κ L` and `residue Rh`, so no
unrelated isomorphism between `L` and the residue field of `Rh` can witness the class. (4) The
instantiation is not degenerate: for `R` henselian local — a field `K`, or `ℤ_[p]` — the identity
`R → R` satisfies all three fields at `L = κ`, because `R` is étale over `R` and hence ind-étale by
`CategoryTheory.ObjectProperty.le_ind`, so the class is inhabited; while for `R = ℤ` localized at
`p` the henselization at `L = κ` is a proper subring of `ℤ_[p]`, and for `R = ℤ_[p]` and
`L = 𝔽_p^sep` a ring satisfying the class is the ring of integers of the maximal unramified
extension of `ℚ_[p]`, so the notion is not satisfied by `R` itself.

## References

* [StacksProject 04GQ](https://stacks.math.columbia.edu/tag/04GQ), Definition 10.155.3
* [StacksProject 04GN](https://stacks.math.columbia.edu/tag/04GN), existence of `R → R^h`
* [StacksProject 04GP](https://stacks.math.columbia.edu/tag/04GP), existence of `R → R^{sh}`
* [StacksProject 08HT](https://stacks.math.columbia.edu/tag/08HT), uniqueness up to unique
  isomorphism, which is what makes the definite article and item (3) legitimate
* [StacksProject 0BSL](https://stacks.math.columbia.edu/tag/0BSL), the intermediate residue
  extensions

## Tags

henselization, strict henselization, henselian local ring, strictly henselian, separable algebraic
closure, ind-étale, étale algebra, filtered colimit, residue field
-/



@[expose] public section

open IsLocalRing in
/-- **Henselization of a local ring** (Stacks 04GQ). Let `(R, 𝔪, κ)` be a local ring and let
`κ ⊆ L` be an extension of its residue field. A local `R`-algebra `Rh` is a *henselization of `R`
with residue field `L`* if `Rh` is henselian, is a filtered colimit of étale `R`-algebras, and has
residue field `L` compatibly with `κ ⊆ L`. For `L = κ` this is the henselization `R → R^h` of
Lemma 04GN, and for `L = κ^sep` a separable algebraic closure of `κ` it is a strict henselization
`R → R^{sh}` of `R` with respect to `κ ⊆ κ^sep`, in the sense of Lemma 04GP; by Lemma 08HT such an
`Rh` is unique up to a unique `R`-algebra isomorphism over `L`. -/
@[stacks 04GQ "One predicate for the source's three items: part (1) is
`IsHenselization R (ResidueField R) Rh`, part (2) is `IsHenselization R κsep Rsh` for
`κ ⊆ κ^sep` a separable algebraic closure, and part (3) is the isomorphism invariance of the
three fields, which by Lemma 08HT makes them equivalent to being isomorphic to a ring Lemma 04GP
constructs. `Rh` being a filtered colimit of étale `R`-algebras is `(CommAlgCat.etale R).ind`, as
in Lemmas 04GN and 04GP, and the residue field condition is item (5) of Lemma 04GP. Locality of
`R → Rh` and `𝔪 Rh = 𝔪_{Rh}` are consequences, not fields. See the module docstring.",
  ega "IV 18.8.7"]
public class IsLocalRing.IsHenselization (R : Type u) [CommRing R] [IsLocalRing R]
    (L : Type v) [Field L] [Algebra (ResidueField R) L]
    (Rh : Type w) [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh] : Prop where
  /-- A henselization is a henselian local ring. -/
  henselian : HenselianLocalRing Rh
  /-- A henselization of `R` is a filtered colimit of étale `R`-algebras, i.e. an ind-étale
  `R`-algebra. -/
  ind_etale : (CommAlgCat.etale.{max u w} R).ind.{max u w}
    (CommAlgCat.of R (ULift.{u} Rh))
  /-- The residue field of a henselization of `R` with residue field `L` is `L`, compatibly with
  the given extension `κ ⊆ L` of the residue field of `R`. -/
  exists_residueFieldEquiv : ∃ e : L ≃+* ResidueField Rh, ∀ x : R,
    e (algebraMap (ResidueField R) L (residue R x)) = residue Rh (algebraMap R Rh x)


namespace IsLocalRing.IsHenselization

open CategoryTheory CategoryTheory.Limits IsLocalRing

/-- In a common universe, the lifted colimit condition is the usual ind-étale condition. -/
public theorem ind_etale_of_universe_le {R : Type u} [CommRing R] [IsLocalRing R]
    (L : Type v) [Field L] [Algebra (ResidueField R) L]
    {Rh : Type (max u w)} [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [IsHenselization R L Rh] :
    (CommAlgCat.etale.{max u w} R).ind.{max u w} (CommAlgCat.of R Rh) :=
  (CommAlgCat.etale R).ind.prop_of_iso (CommAlgCat.isoMk (ULift.algEquiv : ULift.{u} Rh ≃ₐ[R] Rh))
    (ind_etale (R := R) (L := L) (Rh := Rh))

/-- Construct a henselization from an unlifted presentation in a common universe. -/
public theorem of_ind_etale {R : Type u} [CommRing R] [IsLocalRing R]
    {L : Type v} [Field L] [Algebra (ResidueField R) L]
    {Rh : Type (max u w)} [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    (hh : HenselianLocalRing Rh)
    (hi : (CommAlgCat.etale.{max u w} R).ind.{max u w} (CommAlgCat.of R Rh))
    (he : ∃ e : L ≃+* ResidueField Rh, ∀ x : R,
      e (algebraMap (ResidueField R) L (residue R x)) = residue Rh (algebraMap R Rh x)) :
    IsHenselization R L Rh :=
  ⟨hh, (CommAlgCat.etale R).ind.prop_of_iso
    (CommAlgCat.isoMk (ULift.algEquiv : ULift.{u} Rh ≃ₐ[R] Rh).symm) hi, he⟩

/-- The structure map of a henselization is local. This follows from the compatible
identification of its residue field with the prescribed extension of the residue field of `R`. -/
public theorem isLocalHom {R : Type u} [CommRing R] [IsLocalRing R]
    {L : Type v} [Field L] [Algebra (ResidueField R) L]
    {Rh : Type w} [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [IsHenselization R L Rh] : IsLocalHom (algebraMap R Rh) := by
  obtain ⟨e, he⟩ := exists_residueFieldEquiv (R := R) (L := L) (Rh := Rh)
  apply ((local_hom_TFAE (algebraMap R Rh)).out 4 1).mp
  intro x hx
  apply (residue_eq_zero_iff _).mp
  rw [← he x, (residue_eq_zero_iff _).mpr hx, map_zero, map_zero]

private theorem exists_rep_fin {R : Type u} [CommRing R]
    {J : Type w} [Category J] [IsFiltered J] {F : J ⥤ CommAlgCat.{w} R}
    (c : Cocone F) (hc : IsColimit c) {l : ℕ} (x : Fin l → (c.pt : Type w)) :
    ∃ j : J, ∃ y : Fin l → (F.obj j : Type w), ∀ i, (c.ι.app j).hom (y i) = x i := by
  classical
  have : Nonempty J := IsFiltered.nonempty
  choose j y hy using fun i => CommAlgCat.exists_app_eq hc (x i)
  obtain ⟨k, hk⟩ := (CommAlgCat.directed_range c).finset_le (Finset.univ.image j)
  choose z hz using fun i => hk (j i) (Finset.mem_image_of_mem _ (Finset.mem_univ i)) ⟨y i, hy i⟩
  exact ⟨k, z, hz⟩

/-- Forgetting the algebra structure preserves the given filtered colimit. -/
private noncomputable def isColimitForget {R : Type u} [CommRing R]
    {J : Type w} [Category J] [IsFiltered J] {F : J ⥤ CommAlgCat.{w} R}
    (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((forget₂ (CommAlgCat.{w} R) CommRingCat).mapCocone c) := by
  classical
  let D := F ⋙ forget₂ (CommAlgCat.{w} R) CommRingCat
  let j₀ : J := IsFiltered.nonempty.some
  letI : Algebra R (colimit D : CommRingCat) :=
    ((colimit.ι D j₀).hom.comp (algebraMap R (F.obj j₀))).toAlgebra
  have hcomm (j : J) (r : R) :
      (colimit.ι D j).hom (algebraMap R (F.obj j) r) =
        algebraMap R (colimit D : CommRingCat) r := by
    change (colimit.ι D j).hom (algebraMap R (F.obj j) r) =
      (colimit.ι D j₀).hom (algebraMap R (F.obj j₀) r)
    rw [← colimit.w D (IsFiltered.leftToMax j j₀),
      ← colimit.w D (IsFiltered.rightToMax j j₀)]
    change (colimit.ι D _).hom ((F.map _).hom (algebraMap R _ r)) =
      (colimit.ι D _).hom ((F.map _).hom (algebraMap R _ r))
    rw [AlgHom.commutes, AlgHom.commutes]
  let d : Cocone F :=
    { pt := CommAlgCat.of R (colimit D : CommRingCat)
      ι.app j := CommAlgCat.ofHom { __ := (colimit.ι D j).hom, commutes' := hcomm j }
      ι.naturality i j f := by
        apply CommAlgCat.hom_ext
        ext x
        exact ConcreteCategory.congr_hom (colimit.w D f) x }
  refine
    { desc := fun t => CommRingCat.ofHom
        ((colimit.desc D t).hom.comp (hc.desc d).hom.toRingHom)
      fac := ?_
      uniq := ?_ }
  · intro t j
    ext x
    change (colimit.desc D t).hom ((hc.desc d).hom ((c.ι.app j).hom x)) = _
    have h := ConcreteCategory.congr_hom (hc.fac d j) x
    change (hc.desc d).hom ((c.ι.app j).hom x) = (colimit.ι D j).hom x at h
    rw [h]
    exact ConcreteCategory.congr_hom (colimit.ι_desc t j) x
  · intro t m hm
    ext x
    obtain ⟨j, y, rfl⟩ := CommAlgCat.exists_app_eq hc x
    have h := ConcreteCategory.congr_hom (hc.fac d j) y
    change (hc.desc d).hom ((c.ι.app j).hom y) = (colimit.ι D j).hom y at h
    change m.hom ((c.ι.app j).hom y) =
      (colimit.desc D t).hom ((hc.desc d).hom ((c.ι.app j).hom y))
    rw [h]
    exact (ConcreteCategory.congr_hom (hm j) y).trans
      (ConcreteCategory.congr_hom (colimit.ι_desc t j) y).symm

/-- A filtered colimit of étale algebras is flat (Stacks 00U2 and 05UT). -/
public theorem _root_.CommAlgCat.flat_of_ind_etale {R : Type u} {S : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    (hind : (CommAlgCat.etale.{w} R).ind.{w} (CommAlgCat.of R S)) : Module.Flat R S := by
  classical
  obtain ⟨J, _, _, pres, hpres⟩ := hind
  rw [Module.Flat.iff_forall_isTrivialRelation]
  intro l f x hx
  obtain ⟨j, y, hy⟩ := exists_rep_fin pres.cocone pres.isColimit x
  have hz : (pres.ι.app j).hom (∑ i, f i • y i) = (pres.ι.app j).hom 0 := by
    simpa only [map_sum, map_smul, map_zero, hy] using hx
  obtain ⟨k, a, b, hab⟩ := Concrete.isColimit_exists_of_rep_eq
    (pres.diag ⋙ forget₂ (CommAlgCat.{w} R) CommRingCat)
    (isColimitForget pres.cocone pres.isColimit) (∑ i, f i • y i) 0 hz
  have hrel : ∑ i, f i • (pres.diag.map a).hom (y i) = 0 := by
    change (pres.diag.map a).hom (∑ i, f i • y i) = (pres.diag.map b).hom 0 at hab
    simpa only [map_sum, map_smul, map_zero] using hab
  have : Algebra.Etale R (pres.diag.obj k : Type w) := hpres k
  obtain ⟨m, coeff, z, hzrep, hcoeff⟩ :=
    (Module.Flat.iff_forall_isTrivialRelation.mp (inferInstance : Module.Flat R
      (pres.diag.obj k : Type w))) hrel
  refine ⟨m, coeff, fun q => (pres.ι.app k).hom (z q), ?_, hcoeff⟩
  intro i
  rw [← hy i]
  calc
    (pres.ι.app j).hom (y i) = (pres.ι.app k).hom ((pres.diag.map a).hom (y i)) :=
      (ConcreteCategory.congr_hom (pres.w a) (y i)).symm
    _ = _ := by simp only [hzrep i, map_sum, map_smul]

/-- Flatness over the base implies flatness over an ind-étale algebra. Every finite
relation has its coefficients in one étale stage, where this is the unramified case. -/
public theorem _root_.CommAlgCat.flat_of_ind_etale_restrictScalars
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Module.Flat R B]
    (hind : (CommAlgCat.etale.{v} R).ind.{v} (CommAlgCat.of R A)) :
    Module.Flat A B := by
  classical
  obtain ⟨J, _, _, pres, hpres⟩ := hind
  rw [Module.Flat.iff_forall_isTrivialRelation]
  intro l f x hx
  obtain ⟨j, g, hg⟩ := exists_rep_fin pres.cocone pres.isColimit f
  let T := (pres.diag.obj j : Type v)
  let φ : T →ₐ[R] A := (pres.ι.app j).hom
  let : Algebra T B := ((algebraMap A B).comp φ.toRingHom).toAlgebra
  have : IsScalarTower R T B := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap R B r = algebraMap A B (φ (algebraMap R T r))
    rw [φ.commutes, ← IsScalarTower.algebraMap_apply R A B]
  have : Algebra.Etale R T := hpres j
  have : Module.Flat T B := Algebra.FormallyUnramified.flat_of_restrictScalars R T B
  have hs (c : T) (b : B) : c • b = φ c • b := by
    rw [Algebra.smul_def, Algebra.smul_def]; rfl
  have hrel : ∑ i, g i • x i = 0 := by simpa only [hs, φ, hg] using hx
  obtain ⟨m, coeff, z, hz, hcoeff⟩ :=
    (Module.Flat.iff_forall_isTrivialRelation.mp (inferInstance : Module.Flat T B)) hrel
  refine ⟨m, fun i k => φ (coeff i k), z, ?_, ?_⟩
  · intro i
    simpa only [hs] using hz i
  · intro k
    simpa only [map_sum, map_mul, φ, hg, map_zero] using congrArg φ (hcoeff k)

private theorem exists_mul_mem_map_maximalIdeal {R : Type u} {A : Type w}
    [CommRing R] [IsLocalRing R]
    [CommRing A] [Algebra R A] [Algebra.Etale R A] (q : Ideal A) [q.IsPrime]
    [q.LiesOver (maximalIdeal R)] {y : A} (hy : y ∈ q) :
    ∃ g ∉ q, g * y ∈ (maximalIdeal R).map (algebraMap R A) := by
  have hlocal : IsLocalHom (algebraMap R (Localization.AtPrime q)) := by
    refine ((local_hom_TFAE (algebraMap R (Localization.AtPrime q))).out 4 1).1 fun r hr => ?_
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply R A (Localization.AtPrime q)]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q _).2
      ((Ideal.mem_of_liesOver q (maximalIdeal R) r).1 hr)
  have h : algebraMap A (Localization.AtPrime q) y ∈ maximalIdeal (Localization.AtPrime q) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q y).2 hy
  rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R),
    IsScalarTower.algebraMap_eq R A (Localization.AtPrime q), ← Ideal.map_map] at h
  exact (IsLocalization.algebraMap_mem_map_algebraMap_iff (M := q.primeCompl)
    (S := Localization.AtPrime q) _ _).1 h

/-- The maximal ideal of a local ind-étale algebra is extended from the base. -/
public theorem _root_.CommAlgCat.map_maximalIdeal_of_ind_etale {R : Type u} {S : Type w}
    [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)]
    (hind : (CommAlgCat.etale.{w} R).ind.{w} (CommAlgCat.of R S)) :
    (maximalIdeal R).map (algebraMap R S) = maximalIdeal S := by
  classical
  obtain ⟨J, _, _, pres, hpres⟩ := hind
  apply le_antisymm
  · exact Ideal.map_le_iff_le_comap.2 (maximalIdeal_comap (algebraMap R S)).ge
  · intro x hx
    obtain ⟨j, y, hy⟩ := CommAlgCat.exists_app_eq pres.isColimit x
    let q := (maximalIdeal S).comap (pres.ι.app j).hom
    have : (maximalIdeal S).IsPrime := (maximalIdeal.isMaximal S).isPrime
    have : q.IsPrime := Ideal.IsPrime.comap (pres.ι.app j).hom
    have hq : q.LiesOver (maximalIdeal R) := ⟨by
      ext r
      rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
      exact ((SetLike.ext_iff.1 (maximalIdeal_comap (algebraMap R S))) r).symm⟩
    have : Algebra.Etale R (pres.diag.obj j : Type w) := hpres j
    have hyq : y ∈ q := by
      show (pres.ι.app j).hom y ∈ maximalIdeal S
      rwa [hy]
    obtain ⟨g, hg, hgy⟩ := exists_mul_mem_map_maximalIdeal (R := R) q hyq
    let gs : S := (pres.ι.app j).hom g
    have hgu : IsUnit gs := notMem_maximalIdeal.mp (by simpa [gs, q] using hg)
    rw [← hy]
    have hprod := Stacks.Henselization.EtaleColimit.mem_map_of_algHom
      (R := R) (A := (pres.diag.obj j : Type w)) (B := S) (pres.ι.app j).hom hgy
    simp only [map_mul] at hprod
    exact (Ideal.unit_mul_mem_iff_mem _ hgu).mp hprod

/-- A henselization is flat over its base ring, since it is a filtered colimit of étale
algebras. -/
public theorem flat {R : Type u} [CommRing R] [IsLocalRing R]
    {L : Type v} [Field L] [Algebra (ResidueField R) L]
    {Rh : Type w} [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [IsHenselization R L Rh] : Module.Flat R Rh := by
  have : Module.Flat R (ULift.{u} Rh) :=
    CommAlgCat.flat_of_ind_etale (ind_etale (R := R) (L := L) (Rh := Rh))
  exact Module.Flat.of_linearEquiv (ULift.algEquiv : ULift.{u} Rh ≃ₐ[R] Rh).symm.toLinearEquiv

/-- A henselization of a local ring is faithfully flat. -/
public theorem faithfullyFlat {R : Type u} [CommRing R] [IsLocalRing R]
    {L : Type v} [Field L] [Algebra (ResidueField R) L]
    {Rh : Type w} [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [IsHenselization R L Rh] : Module.FaithfullyFlat R Rh :=
  have : Module.Flat R Rh := flat (L := L)
  have : IsLocalHom (algebraMap R Rh) := isLocalHom (L := L)
  Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The maximal ideal of a henselization is generated by the maximal ideal of its base. -/
@[ega "IV 18.6.6" "(iii) 𝔪·^hA maximal"]
public theorem map_maximalIdeal {R : Type u} [CommRing R] [IsLocalRing R]
    {L : Type v} [Field L] [Algebra (ResidueField R) L]
    {Rh : Type w} [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [IsHenselization R L Rh] :
    (maximalIdeal R).map (algebraMap R Rh) = maximalIdeal Rh := by
  have : IsLocalHom (algebraMap R Rh) := isLocalHom (L := L)
  let e : ULift.{u} Rh ≃ₐ[R] Rh := ULift.algEquiv
  have : IsLocalRing (ULift.{u} Rh) := e.symm.toRingEquiv.isLocalRing
  have he : e.toRingHom.comp (algebraMap R (ULift.{u} Rh)) = algebraMap R Rh :=
    e.toAlgHom.comp_algebraMap
  have : IsLocalHom (algebraMap R (ULift.{u} Rh)) := by
    rw [← e.symm.toAlgHom.comp_algebraMap]
    infer_instance
  have h := CommAlgCat.map_maximalIdeal_of_ind_etale
    (ind_etale (R := R) (L := L) (Rh := Rh))
  have h' := congrArg (Ideal.map e.toRingHom) h
  simpa only [Ideal.map_map, he,
    map_maximalIdeal_of_surjective e.toRingHom e.surjective] using h'

end IsLocalRing.IsHenselization

namespace Stacks.Henselization.Shared

open CategoryTheory CategoryTheory.Limits IsLocalRing

/-- Restriction of scalars along a ring equivalence `e : R ≃+* S`, as a functor from
commutative `S`-algebras to commutative `R`-algebras. -/
public def commAlgCatRestrictScalars {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) : CommAlgCat.{w} S ⥤ CommAlgCat.{w} R where
  obj A := by
    letI : Algebra R A := ((algebraMap S A).comp e.toRingHom).toAlgebra
    exact CommAlgCat.of R A
  map {A B} f := by
    letI : Algebra R A := ((algebraMap S A).comp e.toRingHom).toAlgebra
    letI : Algebra R B := ((algebraMap S B).comp e.toRingHom).toAlgebra
    exact CommAlgCat.ofHom
      { f.hom.toRingHom with commutes' := fun r => f.hom.commutes (e r) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Restriction of scalars along a ring equivalence is an equivalence of categories of
commutative algebras. -/
public def commAlgCatRestrictScalarsEquivalence {R : Type u} {S : Type v} [CommRing R]
    [CommRing S] (e : R ≃+* S) : CommAlgCat.{w} S ≌ CommAlgCat.{w} R where
  functor := commAlgCatRestrictScalars e
  inverse := commAlgCatRestrictScalars e.symm
  unitIso := NatIso.ofComponents (fun A => CommAlgCat.isoMk <|
    @AlgEquiv.ofRingEquiv (f := RingEquiv.refl _) _ _ _ _ _ _ A.algebra
      ((commAlgCatRestrictScalars e.symm).obj ((commAlgCatRestrictScalars e).obj A)).algebra
      (fun s => by
        change algebraMap S A s = algebraMap S A (e (e.symm s))
        rw [e.apply_symm_apply]))
  counitIso := NatIso.ofComponents (fun A => CommAlgCat.isoMk <|
    @AlgEquiv.ofRingEquiv (f := RingEquiv.refl _) _ _ _ _ _ _
      ((commAlgCatRestrictScalars e).obj
        ((commAlgCatRestrictScalars e.symm).obj A)).algebra A.algebra
      (fun r => by
        change algebraMap R A (e.symm (e r)) = algebraMap R A r
        rw [e.symm_apply_apply]))

/-- An ind-étale algebra stays ind-étale after restricting scalars along an isomorphism of base
rings: the isomorphism is itself étale, so the étale stages remain étale. -/
public theorem ind_etale_restrictScalars {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) (A : CommAlgCat.{w} S) (h : (CommAlgCat.etale S).ind.{w} A) :
    (CommAlgCat.etale R).ind.{w} ((commAlgCatRestrictScalars e).obj A) := by
  obtain ⟨J, _, _, pres, het⟩ := h
  refine ⟨J, inferInstance, inferInstance,
    pres.map (commAlgCatRestrictScalarsEquivalence e).functor, fun j => ?_⟩
  let : Algebra R S := e.toRingHom.toAlgebra
  let : Algebra R (pres.diag.obj j) :=
    ((algebraMap S (pres.diag.obj j)).comp e.toRingHom).toAlgebra
  have : IsScalarTower R S (pres.diag.obj j) := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.Etale R S :=
    Algebra.Etale.of_equiv (show R ≃ₐ[R] S from { e with commutes' := fun _ => rfl })
  have : Algebra.Etale S (pres.diag.obj j) := het j
  exact Algebra.Etale.comp R S (pres.diag.obj j)

end Stacks.Henselization.Shared

end
