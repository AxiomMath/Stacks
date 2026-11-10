module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeDecency
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.SinglePointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal

/-!
# Radicial morphisms of algebraic spaces

A morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is *radicial* when, for every
field `k` and every `k`-valued point `Spec(k) ⟶ Y`, the reduction of the fibre
`Spec(k) ×_Y X` is either empty or is the spectrum of a purely inseparable field extension
of `k`.

The fibre is the presheaf fibre product, which is again an algebraic space by
`AlgebraicGeometry.isAlgebraicSpace_pullback`, and its reduction is the reduced closed
subspace `AlgebraicGeometry.Space.reducedClosedSubspace` on all of its points. Being the
spectrum of a purely inseparable extension of `k` is recorded as the existence of a purely
inseparable extension `k ⊂ L`, an object `U` of the site whose underlying scheme is
`Spec(L)`, and an isomorphism of the reduction with the presheaf represented by `U` which
is compatible with the two structural morphisms down to `Spec(k)`.

## Main definitions

* `AlgebraicGeometry.Space.IsRadicial`: **Stacks 0481**, the field-valued fibre criterion.
* `AlgebraicGeometry.Space.IsWeaklyRadicial`: **Stacks 049E**, the weaker field-valued fibre
  criterion in which the fibre is asked to have a singleton point set and to receive a
  monomorphism from the spectrum of a purely inseparable extension of the field.

## Main results

* `AlgebraicGeometry.Space.universallyInjective_of_isRadicial`: **Stacks 0482**, a radicial
  morphism is universally injective.
* `AlgebraicGeometry.Space.isRadicial_of_universallyInjective_of_isDecent`,
  `AlgebraicGeometry.Space.isRadicial_of_universallyInjective_of_isQuasiSeparated` and
  `AlgebraicGeometry.Space.isRadicial_of_universallyInjective_of_isLocallySeparated`:
  **Stacks 0484**, the three converses — a universally injective morphism which is
  decent, quasi-separated or locally separated is radicial.
* `AlgebraicGeometry.Space.surjective_app_of_isWeaklyRadicial`: **Stacks 049E**, a weakly
  radicial morphism is surjective on `k`-valued points for every algebraically closed field
  `k` in the site; and `AlgebraicGeometry.Space.isSurjective_of_isWeaklyRadicial`, a weakly
  radicial morphism is surjective.
* `AlgebraicGeometry.Space.isWeaklyRadicial_of_universallyInjective_of_hasPropertyBeta`:
  **Stacks 049E**, the analogue of Stacks 0484 — a surjective universally injective morphism with
  property `(β)` is weakly radicial — and
  `AlgebraicGeometry.Space.exists_universallyInjective_hasPropertyBeta_not_isWeaklyRadicial`, the
  counterexample showing that the surjectivity hypothesis, absent from the source, is needed.

## Implementation notes

"Empty" is taken to mean that the reduction has no field-valued point, which is the right
reading for a presheaf: the empty algebraic space does have a section over the spectrum of
the zero ring, so asking for the presheaf itself to be pointwise empty would be strictly
stronger.

The field `k` is tested through an object `T` of the chosen size-bounded big fppf site
together with an isomorphism of its underlying scheme with `Spec(k)`, exactly as the test by
field-valued points in `AlgebraicGeometry.Space.UniversallyInjective` is, and the extension
`L` is produced in the same shape. The compatibility `(BigFppfOver.toScheme B S hS).map m =
eU.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ eT.inv` is what makes the
isomorphism an isomorphism *over* `Spec(k)`, so that the reduction is identified with
`Spec(L)` as a `k`-scheme and not merely abstractly.

The algebraicity hypotheses on the source and the target are explicit arguments: they are
what the fibre product needs in order to be an algebraic space, hence what the reduced closed
subspace needs in order to exist.

For the converses, the reduction of the fibre over a field-valued point is a reduced closed
subspace of the fibre, so it is reduced and its inclusion is a monomorphism; universal
injectivity makes its point set a subsingleton, and decency of the morphism makes it a decent
algebraic space, a monomorphism being quasi-separated and hence decent. A nonempty one is
therefore the spectrum of a field by Stacks 047Z, and the extension is purely inseparable
because the spectrum map inherits universal injectivity from the morphism, read through the
surjectivity of its relative diagonal.

For the weak notion, "`|Spec(K) ×_Y X|` is a singleton" is `Nonempty` together with
`Subsingleton` on the point set of Stacks 03BU, as elsewhere in the library, and the
monomorphism from `Spec(L)` is a monomorphism of presheaves out of the one represented by an
object whose underlying scheme is `Spec(L)`, together with the same compatibility over
`Spec(K)` as for the radicial condition. The extension `K ⊂ L` is thereby the one induced by
the composition of the monomorphism with the projection to `Spec(K)`, which is what makes
clause (3) a condition on that composition rather than on an unrelated embedding. The
algebraicity hypotheses are recorded in the shape of the radicial condition although the weak
condition speaks only of point sets and of monomorphisms of presheaves.

The surjectivity hypothesis in the source's consequence is automatic: the existence of the
monomorphism already makes every field-valued fibre nonempty, which is
`AlgebraicGeometry.Space.isSurjective_of_isWeaklyRadicial`, so the consequence is stated
without it.

The source's analogue of Stacks 0484 — property `(β)` and universal injectivity imply weakly
radicial, "proof omitted" — is false as stated, because the definition asks every field-valued
fibre to be a singleton, hence nonempty: the inclusion of the empty scheme into the spectrum of a
field is universally injective with property `(β)` and is not weakly radicial. It is proved
here with surjectivity added, which is necessary, a weakly radicial morphism being surjective.
The proof is that of Stacks 0484, with condition (4) of Stacks 03JU, a monomorphism from the
spectrum of a field representing the unique point of the fibre, in place of decency.

## References

* [Stacks Project, Tag 0481](https://stacks.math.columbia.edu/tag/0481)
* [Stacks Project, Tag 0482](https://stacks.math.columbia.edu/tag/0482)
* [Stacks Project, Tag 0484](https://stacks.math.columbia.edu/tag/0484)
* [Stacks Project, Tag 049E](https://stacks.math.columbia.edu/tag/049E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

set_option synthInstance.maxHeartbeats 400000 in
-- `HasPullbacks` search for presheaves on the big fppf site
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_Radicial (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- Shortcut for a single pullback of presheaves on the big fppf site over `S`. -/
local instance (priority := high) hasPullback_presheaf_Radicial (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Stacks 0481.** A morphism of algebraic spaces over `S` is *radicial* if for every
field `k` in the chosen site and every `k`-valued point of the target, the reduction of the
fibre is either empty or is represented, over `Spec(k)`, by the spectrum of a purely
inseparable extension of `k`. -/
@[stacks 0481]
def IsRadicial (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) : Prop :=
  ∀ (k : Type u) [Field k] (T : BigFppfOver B S hS)
    (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of k))
    (g : yoneda.obj T ⟶ Y),
    let P := pullback g f
    let hP : IsAlgebraicSpace B S hS P :=
      isAlgebraicSpace_pullback B S hS g f (isAlgebraicSpace_yoneda B S hS T) hX hY
    letI : TopologicalSpace (points B S hS P) := pointTopology B S hS P
    let Z := reducedClosedSubspace B S hS P hP Set.univ isClosed_univ
    IsEmpty (points B S hS Z.toFunctor) ∨
      ∃ (L : Type u) (hL : Field L) (hAlg : Algebra k L),
        letI := hL
        letI := hAlg
        IsPurelyInseparable k L ∧
          ∃ (U : BigFppfOver B S hS) (m : U ⟶ T)
            (eU : (BigFppfOver.toScheme B S hS).obj U ≅ Spec (.of L))
            (e : Z.toFunctor ≅ yoneda.obj U),
            (e.inv ≫ Z.ι ≫ pullback.fst g f = yoneda.map m) ∧
              ((BigFppfOver.toScheme B S hS).map m =
                eU.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ eT.inv)


/-! ### Universal injectivity -/

private theorem specMap_section_unique
    {K L : Type u} [CommRing K] [Nontrivial K] [Field L] [Algebra K L]
    {a b : Spec (.of K) ⟶ Spec (.of L)}
    (ha : a ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) = 𝟙 _)
    (hb : b ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) = 𝟙 _) : a = b := by
  have hcomp (t : Spec (.of K) ⟶ Spec (.of L))
      (ht : t ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) = 𝟙 _) :
      CommRingCat.ofHom (algebraMap K L) ≫ Spec.homEquiv t = 𝟙 _ := by
    apply Spec.map_injective
    simpa using ht
  have hsurj (l : L) : algebraMap K L ((Spec.homEquiv b).hom l) = l := by
    apply (Spec.homEquiv b).hom.injective
    simpa using congrArg (fun t : CommRingCat.of K ⟶ CommRingCat.of K =>
      t.hom ((Spec.homEquiv b).hom l)) (hcomp b hb)
  apply Spec.homEquiv.injective
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro l
  calc
    (Spec.homEquiv a).hom l = (Spec.homEquiv a).hom
        (algebraMap K L ((Spec.homEquiv b).hom l)) := by rw [hsurj]
    _ = (Spec.homEquiv b).hom l := by
      simpa using congrArg (fun t : CommRingCat.of K ⟶ CommRingCat.of K =>
        t.hom ((Spec.homEquiv b).hom l)) (hcomp a ha)

private theorem eq_of_comp_yoneda_map_eq_id
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {K L : Type u} [Field K] [Field L] [Algebra K L] {T U : BigFppfOver B S hS} (m : U ⟶ T)
    (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of K))
    (eU : (BigFppfOver.toScheme B S hS).obj U ≅ Spec (.of L))
    (hstruct : (BigFppfOver.toScheme B S hS).map m =
      eU.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ eT.inv)
    {v₁ v₂ : yoneda.obj T ⟶ yoneda.obj U}
    (h₁ : v₁ ≫ yoneda.map m = 𝟙 _) (h₂ : v₂ ≫ yoneda.map m = 𝟙 _) : v₁ = v₂ := by
  have hsection (v : yoneda.obj T ⟶ yoneda.obj U) (hv : v ≫ yoneda.map m = 𝟙 _) :
      (yonedaEquiv v : T ⟶ U) ≫ m = 𝟙 T := by
    apply yoneda.map_injective
    have hvm : v = yoneda.map (yonedaEquiv v) := by
      calc
        v = yonedaEquiv.symm (yonedaEquiv v) := (Equiv.symm_apply_apply _ _).symm
        _ = yoneda.map (yonedaEquiv v) := rfl
    rw [hvm] at hv
    simpa only [← yoneda.map_comp, ← yoneda.map_id] using hv
  have hsectionSpec (m' : T ⟶ U) (hm' : m' ≫ m = 𝟙 T) :
      (eT.inv ≫ (BigFppfOver.toScheme B S hS).map m' ≫ eU.hom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) = 𝟙 _ := by
    have hbase : eU.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) =
        (BigFppfOver.toScheme B S hS).map m ≫ eT.hom := by
      rw [hstruct]
      simp
    simp only [Category.assoc, hbase]
    simp only [← Category.assoc]
    rw [Category.assoc eT.inv
      ((BigFppfOver.toScheme B S hS).map m')
      ((BigFppfOver.toScheme B S hS).map m)]
    rw [← (BigFppfOver.toScheme B S hS).map_comp m' m, hm']
    simp
  have hm : (yonedaEquiv v₁ : T ⟶ U) = yonedaEquiv v₂ :=
    (BigFppfOver.toScheme B S hS).map_injective <| (cancel_mono eU.hom).mp <|
      (cancel_epi eT.inv).mp <| specMap_section_unique
        (hsectionSpec _ (hsection v₁ h₁)) (hsectionSpec _ (hsection v₂ h₂))
  exact yonedaEquiv.injective hm

attribute [local instance] pointTopology in
private theorem exists_lift_reducedClosedSubspace_yoneda
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    {T : BigFppfOver B S hS} (hT : IsReduced ((BigFppfOver.toScheme B S hS).obj T))
    (p : yoneda.obj T ⟶ P) :
    ∃ r : yoneda.obj T ⟶ (reducedClosedSubspace B S hS P hP Set.univ isClosed_univ).toFunctor,
      r ≫ (reducedClosedSubspace B S hS P hP Set.univ isClosed_univ).ι = p :=
  (exists_lift_closedSubspace_iff_pointsMap_range_subset
    B S hS hP (isAlgebraicSpace_yoneda B S hS T) _
    (isClosedSubspace_reducedClosedSubspace B S hS P hP Set.univ isClosed_univ)
    ((exists_atlas_iff_of_representable B S hS
      (yoneda.obj T) (fun V : Scheme.{u} => IsReduced V) T (Iso.refl _)).2 hT) p).2 (by
    intro z _
    rw [range_pointsMap_ι_reducedClosedSubspace B S hS P hP Set.univ isClosed_univ]
    exact Set.mem_univ _)

set_option maxHeartbeats 1000000 in
-- pullbacks and Yoneda lifts of presheaves on the big fppf site, closed by `simp`/`simpa`
set_option synthInstance.maxHeartbeats 400000 in
/-- Two sections of the source of a radicial morphism over a field spectrum in the site with
the same image in the target are equal.

The fibre of the morphism over the common image is an algebraic space, and both sections are
sections of its first projection; they factor through the reduction of the fibre, which the
radicial hypothesis identifies with the spectrum of a purely inseparable extension of the
field over that field. A scheme-theoretic section of such a spectrum over the base field is
unique, so the two factorisations agree, and hence so do the sections. -/
private theorem eq_of_isRadicial_section
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hf : IsRadicial B S hS hX hY f)
    {K : Type u} [Field K] (hKsite : B.Contains (Spec (.of K)))
    (s : Spec (.of K) ⟶ S)
    {x y : X.obj (Opposite.op
      (Over.mk (⟨s⟩ : B.obj hKsite ⟶ B.obj hS) : BigFppfOver B S hS))}
    (hxy : f.app (Opposite.op
        (Over.mk (⟨s⟩ : B.obj hKsite ⟶ B.obj hS) : BigFppfOver B S hS)) x =
      f.app (Opposite.op
        (Over.mk (⟨s⟩ : B.obj hKsite ⟶ B.obj hS) : BigFppfOver B S hS)) y) :
    x = y := by
  classical
  let T : BigFppfOver B S hS := Over.mk (⟨s⟩ : B.obj hKsite ⟶ B.obj hS)
  let ix : yoneda.obj T ⟶ X := yonedaEquiv.symm x
  let iy : yoneda.obj T ⟶ X := yonedaEquiv.symm y
  let g : yoneda.obj T ⟶ Y := ix ≫ f
  have hcomp : iy ≫ f = g := by
    simpa [g, ix, iy] using
      (yonedaEquiv_symm_naturality_right T f y).trans
        ((congrArg yonedaEquiv.symm hxy.symm).trans
          (yonedaEquiv_symm_naturality_right T f x).symm)
  let P := pullback g f
  let hP : IsAlgebraicSpace B S hS P :=
    isAlgebraicSpace_pullback B S hS g f (isAlgebraicSpace_yoneda B S hS T) hX hY
  let _ : TopologicalSpace (points B S hS P) := pointTopology B S hS P
  let Z := reducedClosedSubspace B S hS P hP Set.univ isClosed_univ
  have eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of K) := Iso.refl _
  let p₁ : yoneda.obj T ⟶ P := pullback.lift (𝟙 _) ix (by simp [g, ix])
  let p₂ : yoneda.obj T ⟶ P := pullback.lift (𝟙 _) iy (by simp [hcomp, g, iy])
  have liftZ (p : yoneda.obj T ⟶ P) : ∃ r : yoneda.obj T ⟶ Z.toFunctor, r ≫ Z.ι = p :=
    exists_lift_reducedClosedSubspace_yoneda B S hS hP (by
      change IsReduced (Spec (.of K))
      infer_instance) p
  obtain ⟨r₁, hr₁⟩ := liftZ p₁
  obtain ⟨r₂, hr₂⟩ := liftZ p₂
  rcases hf K T eT g with hempty | ⟨L, hL, hAlg, hPI, U, m, eU, e, hproj, hstruct⟩
  · exact False.elim (hempty.false
      (({ carrier := K, contained := hKsite, toBase := s,
          value := r₁.app (Opposite.op T) (𝟙 T) } :
          FieldValuedPoint B S hS Z.toFunctor).class B S hS Z.toFunctor))
  · let _ : Field L := hL
    let _ : Algebra K L := hAlg
    have hsection (r : yoneda.obj T ⟶ Z.toFunctor)
        (hr : (r ≫ Z.ι) ≫ pullback.fst g f = 𝟙 (yoneda.obj T)) :
        (r ≫ e.hom) ≫ yoneda.map m = 𝟙 _ := by
      rw [hproj.symm]
      simpa [Category.assoc] using hr
    have hr : r₁ = r₂ := (Iso.cancel_iso_hom_right _ _ e).mp <|
      eq_of_comp_yoneda_map_eq_id B S hS m eT eU hstruct
        (hsection r₁ (by rw [hr₁]; simp [p₁]))
        (hsection r₂ (by rw [hr₂]; simp [p₂]))
    have hp : p₁ = p₂ := by rw [← hr₁, ← hr₂, hr]
    have hix : ix = iy := by
      simpa [p₁, p₂, pullback.lift_snd] using congrArg (fun q => q ≫ pullback.snd g f) hp
    apply yonedaEquiv.symm.injective
    simpa [ix, iy] using hix

/-- **Stacks 0482.** A radicial morphism of algebraic spaces is universally injective.

On a field-valued point of the target the fibre's reduction is either empty, excluding the
point, or the spectrum of a purely inseparable extension, and a scheme-theoretic section of
such a spectrum over the base field is unique; two points of the fibre therefore agree. -/
@[stacks 0482, ega "I 3.5.11" "radicial => univ. inj."]
theorem universallyInjective_of_isRadicial
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hf : IsRadicial B S hS hX hY f) :
    UniversallyInjective B S hS f := by
  refine universallyInjective_of_fieldPoints B S hS f fun p y hy ↦ ⟨p, 𝟙 _, by simp, ?_⟩
  have h : p.value = y :=
    eq_of_isRadicial_section B S hS hX hY f hf p.contained p.toBase hy
  simpa using h.symm

/-- The image of a relative diagonal under a pullback-preserving functor is the relative
diagonal of the image, up to the comparison isomorphism. -/
private theorem map_diagonal_comp_preservesPullbackIso
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {U V : C} (m : U ⟶ V) [HasPullback m m]
    [HasPullback (F.map m) (F.map m)] [PreservesLimit (cospan m m) F] :
    F.map (pullback.diagonal m) ≫ (PreservesPullback.iso F m m).hom =
      pullback.diagonal (F.map m) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, PreservesPullback.iso_hom_fst, ← F.map_comp,
      pullback.diagonal_fst, F.map_id]
  · simp only [Category.assoc, PreservesPullback.iso_hom_snd, ← F.map_comp,
      pullback.diagonal_snd, F.map_id]

/-- An extension of fields whose spectrum map is universally injective is purely inseparable:
the induced map on homomorphisms into an algebraic closure is injective. -/
@[ega "IV 6.15.3" "special case"]
private theorem isPurelyInseparable_of_universallyInjective_specMap
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    (h : _root_.AlgebraicGeometry.UniversallyInjective
      (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    IsPurelyInseparable k L := by
  have : Nonempty (L →+* AlgebraicClosure L) := ⟨algebraMap L (AlgebraicClosure L)⟩
  apply IsPurelyInseparable.of_injective_comp_algebraMap k L (AlgebraicClosure L)
  intro a b hab
  have hinj := ((tfae_universallyInjective
    (Spec.map (CommRingCat.ofHom (algebraMap k L)))).out 1 2).mp h
  have heq : Spec.map (CommRingCat.ofHom a) = Spec.map (CommRingCat.ofHom b) := by
    apply hinj (AlgebraicClosure L)
    simpa only [← Spec.map_comp, ← CommRingCat.ofHom_comp] using
      congrArg (fun t => Spec.map (CommRingCat.ofHom t)) hab
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective heq)

/-! ### Universally injective morphisms which are radicial -/

section Converse

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A monomorphism of presheaves on the big fppf site of `S` is universally injective: each of
its base changes is again a monomorphism, and a monomorphism is injective on points. -/
private theorem universallyInjective_of_mono'
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : F ⟶ G) [Mono i] :
    UniversallyInjective B S hS i := by
  intro W _ g
  have : Mono (pullback.fst g i) := inferInstance
  exact pointsMap_injective_of_mono B S hS (pullback.fst g i)

/-- The point set of a presheaf represented by an object of the site whose underlying scheme is
the spectrum of a field is a subsingleton. -/
private theorem subsingleton_points_yoneda_of_isoSpec
    (T : BigFppfOver B S hS) (k : Type u) [Field k]
    (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of k)) :
    Subsingleton (points B S hS (yoneda.obj T)) := by
  have h1 : Subsingleton (Spec (.of k)) := by
    change Subsingleton (PrimeSpectrum k); infer_instance
  have h2 : Subsingleton ((BigFppfOver.toScheme B S hS).obj T) :=
    ⟨fun x y => eT.hom.injective (h1.elim _ _)⟩
  exact (pointsEquivScheme B S hS T).subsingleton

/-- Surjectivity on points of a morphism between presheaves represented by objects of the site
is surjectivity of the underlying morphism of schemes. -/
private theorem surjective_map_of_isSurjective_yoneda
    {M T : BigFppfOver B S hS} (m : M ⟶ T)
    (hm : IsSurjective B S hS (yoneda.map m)) :
    Surjective ((BigFppfOver.toScheme B S hS).map m) :=
  MorphismProperty.of_relative_map
    (P := MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B S hS)) (F := yoneda)
    ((presheafSurjective_iff_isSurjective_yoneda B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T) M (yoneda.map m)).2 hm)

/-- A surjective immersion of algebraic spaces over `S` is a closed immersion: each of its
represented base changes is a surjective immersion of schemes, whose image is therefore the
whole of the target and in particular closed. -/
private theorem isClosedImmersion_of_isImmersion_of_isSurjective
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (h : F ⟶ G) (himm : IsImmersion B S hS h) (hsurj : IsSurjective B S hS h) :
    IsClosedImmersion B S hS h := by
  refine ⟨himm.rep, ?_⟩
  intro a b g fst snd hp
  have : _root_.AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B S hS).map snd) := himm.property g fst snd hp
  have : Surjective ((BigFppfOver.toScheme B S hS).map snd) :=
    ((presheafSurjective_iff_isSurjective B S hS hF hG h himm.rep).2
      hsurj).property g fst snd hp
  change _root_.AlgebraicGeometry.IsClosedImmersion
    ((BigFppfOver.toScheme B S hS).map snd)
  rw [_root_.AlgebraicGeometry.IsClosedImmersion.iff_isPreimmersion]
  refine ⟨inferInstance, ?_⟩
  rw [Set.range_eq_univ.mpr (Scheme.Hom.surjective _)]
  exact isClosed_univ

/-- Universal injectivity of a morphism between presheaves represented by objects of the site
transfers to the underlying morphism of schemes: the relative diagonal is surjective on points,
hence the diagonal of the morphism of schemes is surjective. -/
private theorem universallyInjective_map_of_universallyInjective_yoneda
    {M T : BigFppfOver B S hS} (m : M ⟶ T)
    (hm : UniversallyInjective B S hS (yoneda.map m)) :
    _root_.AlgebraicGeometry.UniversallyInjective
      ((BigFppfOver.toScheme B S hS).map m) := by
  have hd : IsSurjective B S hS (pullback.diagonal (yoneda.map m)) :=
    isSurjective_diagonal_of_universallyInjective B S hS
      (isAlgebraicSpace_yoneda B S hS M) (yoneda.map m) hm
  have hdy : IsSurjective B S hS (yoneda.map (pullback.diagonal m)) := by
    intro y
    obtain ⟨x, hx⟩ := hd (pointsMap B S hS _ (PreservesPullback.iso yoneda m m).hom y)
    refine ⟨x, (pointsEquivOfIso B S hS (PreservesPullback.iso yoneda m m)).injective ?_⟩
    change pointsMap B S hS _ (PreservesPullback.iso yoneda m m).hom
      (pointsMap B S hS _ (yoneda.map (pullback.diagonal m)) x) = _
    rw [← pointsMap_comp_apply, map_diagonal_comp_preservesPullbackIso]
    exact hx
  have hsurj := surjective_map_of_isSurjective_yoneda B S hS (pullback.diagonal m) hdy
  apply (_root_.AlgebraicGeometry.UniversallyInjective.iff_diagonal
    ((BigFppfOver.toScheme B S hS).map m)).2
  rw [← map_diagonal_comp_preservesPullbackIso (BigFppfOver.toScheme B S hS) m]
  infer_instance

private theorem exists_isPurelyInseparable_of_universallyInjective_yoneda
    {k L : Type u} [Field k] [Field L] {M T : BigFppfOver B S hS} (m : M ⟶ T)
    (eU : (BigFppfOver.toScheme B S hS).obj M ≅ Spec (.of L))
    (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of k))
    (hinjm : UniversallyInjective B S hS (yoneda.map m)) :
    ∃ _ : Algebra k L, IsPurelyInseparable k L ∧
      (BigFppfOver.toScheme B S hS).map m =
        eU.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ eT.inv := by
  let Q := BigFppfOver.toScheme B S hS
  have hinjQ : _root_.AlgebraicGeometry.UniversallyInjective (Q.map m) :=
    universallyInjective_map_of_universallyInjective_yoneda B S hS m hinjm
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (eU.inv ≫ Q.map m ≫ eT.hom)
  let inst : Algebra k L := (show k →+* L from CommRingCat.Hom.hom φ).toAlgebra
  have hofhom : CommRingCat.ofHom (algebraMap k L) = φ := rfl
  have hpure : IsPurelyInseparable k L := by
    apply isPurelyInseparable_of_universallyInjective_specMap
    rw [hofhom, hφ]
    exact MorphismProperty.comp_mem
      (@_root_.AlgebraicGeometry.UniversallyInjective) _ _ inferInstance
      (MorphismProperty.comp_mem
        (@_root_.AlgebraicGeometry.UniversallyInjective) _ _ hinjQ inferInstance)
  refine ⟨inst, hpure, ?_⟩
  rw [hofhom, hφ]
  simp
  rfl

/-- If a morphism is universally injective, then the fibre over a point of the target given by an
object of the site over a field has a subsingleton point set. -/
private theorem subsingleton_points_pullback_of_universallyInjective
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (hinj : UniversallyInjective B S hS f)
    {T : BigFppfOver B S hS} {k : Type u} [Field k]
    (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of k)) (g : yoneda.obj T ⟶ Y) :
    Subsingleton (points B S hS (pullback g f)) :=
  have := subsingleton_points_yoneda_of_isoSpec B S hS T k eT
  ⟨fun _ _ => hinj (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) g (Subsingleton.elim _ _)⟩

/-- A monomorphism from a representable presheaf, whose scheme is a field spectrum `Spec(L)`,
into the fibre of a universally injective morphism over a field spectrum `Spec(k)` gives a purely
inseparable extension `k ⊂ L` and a morphism of the site lifting its composite with the first
projection. -/
private theorem exists_isPurelyInseparable_of_mono_pullback
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hinj : UniversallyInjective B S hS f)
    {k L : Type u} [Field k] [Field L] {M T : BigFppfOver B S hS}
    (eU : (BigFppfOver.toScheme B S hS).obj M ≅ Spec (.of L))
    (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of k))
    (g : yoneda.obj T ⟶ Y) (i : yoneda.obj M ⟶ pullback g f) [Mono i] :
    ∃ (m : M ⟶ T) (_ : Algebra k L), IsPurelyInseparable k L ∧
      yoneda.map m = i ≫ pullback.fst g f ∧
      (BigFppfOver.toScheme B S hS).map m =
        eU.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) ≫ eT.inv := by
  have hm : yoneda.map (yoneda.preimage (i ≫ pullback.fst g f)) = i ≫ pullback.fst g f :=
    yoneda.map_preimage _
  have hinjm : UniversallyInjective B S hS (i ≫ pullback.fst g f) :=
    universallyInjective_comp B S hS
      (isAlgebraicSpace_pullback B S hS g f (isAlgebraicSpace_yoneda B S hS T) hX hY)
      (isAlgebraicSpace_yoneda B S hS T) i (pullback.fst g f)
      (universallyInjective_of_mono' B S hS i) (universallyInjective_pullback B S hS f g hinj)
  obtain ⟨inst, hpure, hstr⟩ := exists_isPurelyInseparable_of_universallyInjective_yoneda B S hS
    (yoneda.preimage (i ≫ pullback.fst g f)) eU eT (by rw [hm]; exact hinjm)
  exact ⟨_, inst, hpure, hm, hstr⟩

set_option maxHeartbeats 1000000 in
-- pullbacks and the reduced closed subspace of presheaves on the big fppf site
set_option synthInstance.maxHeartbeats 400000 in
/-- **Stacks 0484, part (1).** A universally injective decent morphism of algebraic spaces over
`S` is radicial.

Over a field-valued point of the target the reduction of the fibre is a reduced decent algebraic
space whose point set is a subsingleton, hence empty or the spectrum of a field by Stacks 047Z,
and the resulting extension is purely inseparable because its spectrum map is again universally
injective. -/
@[stacks 0484 "part (1)"]
theorem isRadicial_of_universallyInjective_of_isDecent
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hinj : UniversallyInjective B S hS f)
    (hdecent : IsDecent B S hS f) :
    IsRadicial B S hS hX hY f := by
  classical
  intro k _ T eT g
  let P := pullback g f
  let hP : IsAlgebraicSpace B S hS P :=
    isAlgebraicSpace_pullback B S hS g f (isAlgebraicSpace_yoneda B S hS T) hX hY
  let Z := reducedClosedSubspace B S hS P hP Set.univ isClosed_univ
  change IsEmpty (points B S hS Z.toFunctor) ∨ _
  have hPsub := subsingleton_points_pullback_of_universallyInjective B S hS f hinj eT g
  have hZalg : IsAlgebraicSpace B S hS Z.toFunctor :=
    (isClosedSubspace_reducedClosedSubspace B S hS P hP Set.univ isClosed_univ).1
  have hZred : HasEtaleLocalProperty B S hS Z.toFunctor
      (fun W : Scheme.{u} => IsReduced W) :=
    hasEtaleLocalProperty_isReduced_reducedClosedSubspace B S hS P hP Set.univ isClosed_univ
  have hZsub : Subsingleton (points B S hS Z.toFunctor) :=
    ⟨fun x y => pointsMap_injective_of_mono B S hS Z.ι (hPsub.elim _ _)⟩
  have hZdec : IsDecentSpace B S hS Z.toFunctor :=
    isDecentSpace_of_isDecent B S hS hZalg hP Z.ι (hdecent T g)
      (isDecent_of_isReasonable B S hS hZalg hP Z.ι
        (isReasonable_of_isVeryReasonable B S hS hZalg hP
          (isVeryReasonable_of_isQuasiSeparated B S hS hZalg hP
            (isQuasiSeparated_of_mono B S hS Z.ι inferInstance))))
  rcases isEmpty_or_nonempty (points B S hS Z.toFunctor) with hempty | hne
  · exact Or.inl hempty
  right
  obtain ⟨M, L, hL, ⟨eU⟩, ⟨e⟩⟩ :=
    exists_iso_yoneda_spec_of_subsingleton_points B S hS hZalg hZdec hne hZsub hZred
  have hZι : Mono Z.ι := inferInstance
  have : Mono (e.inv ≫ Z.ι) := mono_comp _ _
  obtain ⟨m, inst, hpure, hm, hstr⟩ :=
    exists_isPurelyInseparable_of_mono_pullback B S hS hX hY f hinj eU eT g (e.inv ≫ Z.ι)
  exact ⟨L, hL, inst, hpure, M, m, eU, e, by simpa using hm.symm, hstr⟩

/-- **Stacks 0484, part (2).** A universally injective quasi-separated morphism of algebraic
spaces over `S` is radicial: a quasi-separated morphism is very reasonable, hence reasonable,
hence decent. -/
@[stacks 0484 "part (2)"]
theorem isRadicial_of_universallyInjective_of_isQuasiSeparated
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hinj : UniversallyInjective B S hS f)
    (hqs : IsQuasiSeparated B S hS f) :
    IsRadicial B S hS hX hY f :=
  isRadicial_of_universallyInjective_of_isDecent B S hS hX hY f hinj
    (isDecent_of_isReasonable B S hS hX hY f
      (isReasonable_of_isVeryReasonable B S hS hX hY
        (isVeryReasonable_of_isQuasiSeparated B S hS hX hY hqs)))

/-- **Stacks 0484, part (3).** A universally injective locally separated morphism of algebraic
spaces over `S` is radicial.

Universal injectivity makes the relative diagonal surjective and local separatedness makes it an
immersion, so it is a closed immersion; the morphism is therefore separated, in particular
quasi-separated. -/
@[stacks 0484 "part (3)"]
theorem isRadicial_of_universallyInjective_of_isLocallySeparated
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hinj : UniversallyInjective B S hS f)
    (hls : IsLocallySeparated B S hS f) :
    IsRadicial B S hS hX hY f :=
  isRadicial_of_universallyInjective_of_isQuasiSeparated B S hS hX hY f hinj
    (isQuasiCompact_of_isClosedImmersion' B S hS
      (isClosedImmersion_of_isImmersion_of_isSurjective B S hS hX
        (isAlgebraicSpace_pullback B S hS f f hX hX hY) (pullback.diagonal f) hls
        (isSurjective_diagonal_of_universallyInjective B S hS hX f hinj)))

end Converse

/-! ### Weakly radicial morphisms -/

/-- **Stacks 049E.** A morphism of algebraic spaces over `S` is *weakly radicial* if for every
field `K` in the chosen site and every `K`-valued point of the target, the point set of the fibre
is a singleton and the fibre admits, over `Spec(K)`, a monomorphism from the spectrum of a purely
inseparable extension of `K`. -/
@[stacks 049E "the definition of a weakly radicial morphism"]
def IsWeaklyRadicial (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hX : IsAlgebraicSpace B S hS X) (_hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) : Prop :=
  ∀ (K : Type u) [Field K] (T : BigFppfOver B S hS)
    (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of K))
    (g : yoneda.obj T ⟶ Y),
    let P := pullback g f
    (Nonempty (points B S hS P) ∧ Subsingleton (points B S hS P)) ∧
      ∃ (L : Type u) (hL : Field L) (hAlg : Algebra K L),
        letI := hL
        letI := hAlg
        IsPurelyInseparable K L ∧
          ∃ (U : BigFppfOver B S hS) (m : U ⟶ T)
            (eU : (BigFppfOver.toScheme B S hS).obj U ≅ Spec (.of L))
            (i : yoneda.obj U ⟶ P),
            Mono i ∧ (i ≫ pullback.fst g f = yoneda.map m) ∧
              ((BigFppfOver.toScheme B S hS).map m =
                eU.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ eT.inv)

/-- A weakly radicial morphism of algebraic spaces is surjective.

Every point of the target is the class of a field-valued point, whose associated fibre has a
nonempty point set; the point set of the spectrum of the field is a subsingleton, so the two
projections of such a point of the fibre exhibit the given point of the target as an image. -/
theorem isSurjective_of_isWeaklyRadicial
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsWeaklyRadicial B S hS hX hY f) :
    IsSurjective B S hS f := by
  intro w
  obtain ⟨p, rfl⟩ := Quot.exists_rep w
  let T : BigFppfOver B S hS :=
    Over.mk (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hS)
  let g : yoneda.obj T ⟶ Y := yonedaEquiv.symm p.value
  have eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of p.carrier) := Iso.refl _
  obtain ⟨⟨⟨z⟩, -⟩, -⟩ := hf p.carrier T eT g
  let q : FieldValuedPoint B S hS (yoneda.obj T) :=
    { carrier := p.carrier, contained := p.contained, toBase := p.toBase, value := 𝟙 T }
  refine ⟨pointsMap B S hS (pullback g f) (pullback.snd g f) z, ?_⟩
  have hval : g.app (Opposite.op T) (𝟙 T) = p.value :=
    yonedaEquiv.apply_symm_apply p.value
  have hfst : pointsMap B S hS (pullback g f) (pullback.fst g f) z =
      q.class B S hS (yoneda.obj T) :=
    (subsingleton_points_yoneda_of_isoSpec B S hS T p.carrier eT).elim _ _
  have htarget : pointsMap B S hS (yoneda.obj T) g (q.class B S hS (yoneda.obj T)) =
      p.class B S hS Y := by
    rw [pointsMap_class]
    refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS Y
      ⟨p, ⟨𝟙 _, ?_⟩, FieldValuedPoint.dominates_refl B S hS Y p⟩
    change Y.map (𝟙 (Opposite.op T)) (g.app (Opposite.op T) (𝟙 T)) = p.value
    simpa using hval
  calc pointsMap B S hS X f (pointsMap B S hS (pullback g f) (pullback.snd g f) z)
      = pointsMap B S hS (pullback g f) (pullback.snd g f ≫ f) z := by
        rw [pointsMap_comp]
        rfl
    _ = pointsMap B S hS (pullback g f) (pullback.fst g f ≫ g) z := by
        rw [pullback.condition]
    _ = pointsMap B S hS (yoneda.obj T) g
          (pointsMap B S hS (pullback g f) (pullback.fst g f) z) := by
        rw [pointsMap_comp]
        rfl
    _ = p.class B S hS Y := by rw [hfst, htarget]

/-- **Stacks 049E.** A weakly radicial morphism of algebraic spaces over `S` is surjective on
`k`-valued points for every algebraically closed field `k` in the chosen site.

The fibre over a `k`-valued point of the target receives a monomorphism from the spectrum of a
purely inseparable extension of `k`, and such an extension of an algebraically closed field is
trivial; the induced morphism of field spectra is therefore an isomorphism, and inverting it
produces a section of the fibre's projection, hence a `k`-valued point of the source over the
given one. -/
@[stacks 049E "surjectivity on k-points for k algebraically closed"]
theorem surjective_app_of_isWeaklyRadicial
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsWeaklyRadicial B S hS hX hY f)
    (k : Type u) [Field k] [IsAlgClosed k] (hk : B.Contains (Spec (.of k)))
    (s : Spec (.of k) ⟶ S) :
    Function.Surjective (f.app (Opposite.op
      (Over.mk (⟨s⟩ : B.obj hk ⟶ B.obj hS) : BigFppfOver B S hS))) := by
  intro y
  let T : BigFppfOver B S hS := Over.mk (⟨s⟩ : B.obj hk ⟶ B.obj hS)
  let g : yoneda.obj T ⟶ Y := yonedaEquiv.symm y
  have eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of k) := Iso.refl _
  obtain ⟨-, L, hL, hAlg, hPI, _U, m, _eU, i, -, hproj, hstruct⟩ := hf k T eT g
  have : IsIso (CommRingCat.ofHom (algebraMap k L)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  have : IsIso ((BigFppfOver.toScheme B S hS).map m) := by
    rw [hstruct]
    infer_instance
  have : IsIso m := isIso_of_reflects_iso m (BigFppfOver.toScheme B S hS)
  refine ⟨yonedaEquiv (yoneda.map (inv m) ≫ i ≫ pullback.snd g f), ?_⟩
  have key : (yoneda.map (inv m) ≫ i ≫ pullback.snd g f) ≫ f = g := by
    calc (yoneda.map (inv m) ≫ i ≫ pullback.snd g f) ≫ f
        = yoneda.map (inv m) ≫ (i ≫ pullback.snd g f) ≫ f := by simp
      _ = yoneda.map (inv m) ≫ (i ≫ pullback.fst g f) ≫ g := by
          simp only [Category.assoc, pullback.condition]
      _ = yoneda.map (inv m) ≫ yoneda.map m ≫ g := by rw [hproj]
      _ = g := by
          rw [← Category.assoc, ← yoneda.map_comp, IsIso.inv_hom_id, yoneda.map_id,
            Category.id_comp]
  calc f.app (Opposite.op T) (yonedaEquiv (yoneda.map (inv m) ≫ i ≫ pullback.snd g f))
      = yonedaEquiv ((yoneda.map (inv m) ≫ i ≫ pullback.snd g f) ≫ f) :=
        (yonedaEquiv_comp _ _).symm
    _ = y := by rw [key, Equiv.apply_symm_apply]

/-! ### Property `(β)` and universal injectivity -/

section PropertyBeta

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 049E, the analogue of Stacks 0484.** A surjective, universally injective morphism
of algebraic spaces over `S` with property `(β)` is weakly radicial.

The source states this without the surjectivity hypothesis, and in that form it is false: a weakly
radicial morphism is surjective (`AlgebraicGeometry.Space.isSurjective_of_isWeaklyRadicial`),
while the inclusion of the empty scheme is universally injective and has property `(β)`, see
`AlgebraicGeometry.Space.exists_universallyInjective_hasPropertyBeta_not_isWeaklyRadicial`.

Over a field-valued point `Spec(K) ⟶ Y` the fibre has a subsingleton point set by universal
injectivity and a nonempty one by surjectivity. Property `(β)` at its unique point is
condition (1) of Stacks 03JU, which is equivalent to condition (4): a monomorphism from the
spectrum of a field `L` representing the point. The composite `Spec(L) ⟶ Spec(K)` is
universally injective, a monomorphism being universally injective, so `K ⊂ L` is purely
inseparable, exactly as in the proof of Stacks 0484. -/
@[stacks 049E "analogue of 0484: (β) + universally injective + surjective ⇒ weakly radicial"]
theorem isWeaklyRadicial_of_universallyInjective_of_hasPropertyBeta
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y)
    (hinj : UniversallyInjective B S hS f)
    (hbeta : HasPropertyBeta B S hS f)
    (hsurj : IsSurjective B S hS f) :
    IsWeaklyRadicial B S hS hX hY f := by
  classical
  intro K _ T eT g
  let P := pullback g f
  let hP : IsAlgebraicSpace B S hS P :=
    isAlgebraicSpace_pullback B S hS g f (isAlgebraicSpace_yoneda B S hS T) hX hY
  have hPsub := subsingleton_points_pullback_of_universallyInjective B S hS f hinj eT g
  have hfstSurj : IsSurjective B S hS (pullback.fst g f) :=
    isSurjective_of_isPullback B S hS
      (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (ObjectProperty.homMk g :
          (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
        (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)).flip hsurj
  have t : points B S hS (yoneda.obj T) :=
    (pointsEquivScheme B S hS T).symm (eT.inv (IsLocalRing.closedPoint K))
  obtain ⟨x, -⟩ := hfstSurj t
  refine ⟨⟨⟨x⟩, hPsub⟩, ?_⟩
  obtain ⟨p, -, hmono⟩ :=
    (hasEtaleQuasiCompactFieldRepresentative_iff_hasMonomorphicFieldRepresentative B S hS hP x).1
      ((hasFiniteRelationFiberAtEveryEtaleChart_iff_hasEtaleQuasiCompactFieldRepresentative
        B S hS P hP x).1
        ((hasFiniteRelationFiberAt_iff_everyEtaleChart B S hS P hP x).1 (hbeta T g x)))
  let L := p.carrier
  let M : BigFppfOver B S hS := p.siteObject
  let i : yoneda.obj M ⟶ P := fieldMorphism B S hS P p
  have eU : (BigFppfOver.toScheme B S hS).obj M ≅ Spec (.of L) := Iso.refl _
  obtain ⟨m, inst, hpure, hm, hstr⟩ :=
    exists_isPurelyInseparable_of_mono_pullback B S hS hX hY f hinj eU eT g i
  exact ⟨L, inferInstance, inst, hpure, M, m, eU, i, hmono, hm.symm, hstr⟩

/-- The presheaf represented by an object of the site whose underlying scheme is empty has no
points: a field-valued point would give a morphism from a nonempty field spectrum to it. -/
private theorem isEmpty_points_pullback_yoneda_of_isEmpty
    {Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (E : BigFppfOver B S hS)
    (hE : IsEmpty ((BigFppfOver.toScheme B S hS).obj E))
    (f : yoneda.obj E ⟶ Y) (g : Y' ⟶ Y) :
    IsEmpty (points B S hS (pullback g f)) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨p, -⟩ := Quot.exists_rep x
  let a : p.siteObject ⟶ E := (pullback.snd g f).app _ p.value
  exact hE.false ((BigFppfOver.toScheme B S hS).map a (IsLocalRing.closedPoint p.carrier))

/-- **Stacks 049E, the analogue of Stacks 0484 as stated is false.** As soon as the site
contains the spectrum of a field, there is a universally injective morphism of algebraic
spaces with property `(β)` which is not weakly radicial: the inclusion into `Spec(K)` of the
empty scheme. Its fibre over `Spec(K)` has no point, whereas a weakly radicial morphism has a
one-point fibre over every field-valued point.

The corrected statement, with surjectivity added, is
`AlgebraicGeometry.Space.isWeaklyRadicial_of_universallyInjective_of_hasPropertyBeta`. -/
@[stacks 049E "the analogue of Lemma 0484 without surjectivity is false: a counterexample"]
theorem exists_universallyInjective_hasPropertyBeta_not_isWeaklyRadicial
    (K : Type u) [Field K] (hK : B.Contains (Spec (.of K))) (s : Spec (.of K) ⟶ S) :
    ∃ (X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
      (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y),
      UniversallyInjective B S hS f ∧ HasPropertyBeta B S hS f ∧
        ¬ IsWeaklyRadicial B S hS hX hY f := by
  let T : BigFppfOver B S hS := Over.mk (⟨s⟩ : B.obj hK ⟶ B.obj hS)
  let e : Spec (.of PUnit.{u + 1}) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom
      { toFun := fun _ => PUnit.unit, map_one' := rfl, map_mul' := fun _ _ => rfl,
        map_zero' := rfl, map_add' := fun _ _ => rfl } : CommRingCat.of K ⟶ _)
  have hE : B.Contains (Spec (.of PUnit.{u + 1})) := by
    rw [BigFppfSite.Contains, Scheme.size_Spec]
    exact max_lt B.aleph0_lt_cutoff (lt_of_le_of_lt (by simp) B.aleph0_lt_cutoff)
  let E : BigFppfOver B S hS := Over.mk (⟨e ≫ s⟩ : B.obj hE ⟶ B.obj hS)
  have hEmpty : IsEmpty ((BigFppfOver.toScheme B S hS).obj E) := by
    change IsEmpty (PrimeSpectrum PUnit.{u + 1})
    infer_instance
  let m : E ⟶ T := Over.homMk (ObjectProperty.homMk e) rfl
  refine ⟨yoneda.obj E, yoneda.obj T, isAlgebraicSpace_yoneda B S hS E,
    isAlgebraicSpace_yoneda B S hS T, yoneda.map m, ?_, ?_, ?_⟩
  · intro Y' _ g a
    exact (isEmpty_points_pullback_yoneda_of_isEmpty B S hS E hEmpty _ g).elim a
  · intro T' g
    exact hasFiniteRelationFibersAtEveryPoint_of_isEmpty_points B S hS _
      (isEmpty_points_pullback_yoneda_of_isEmpty B S hS E hEmpty _ g)
  · intro h
    have eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of K) := Iso.refl _
    obtain ⟨⟨⟨x⟩, -⟩, -⟩ := h K T eT (𝟙 _)
    exact (isEmpty_points_pullback_yoneda_of_isEmpty B S hS E hEmpty _ _).elim x

end PropertyBeta

end AlgebraicGeometry.Space

end
