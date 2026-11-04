module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SeparatedAtlas

/-!
# The descended scheme is an object of the size-bounded site

The hypothesis `hAPK` of
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_isEffectiveFpqcDescent` asks for the
descended scheme to be an *object of the big fppf category over `S`*, whereas Stacks 0APK
produces a bare scheme. This file removes that gap: the descended scheme receives a flat
surjective morphism from a scheme already in the site, namely the base change of the covering
morphism, so the site's size cutoff — a strong prelimit cardinal — already contains it.

## Main results

* `AlgebraicGeometry.BigFppfSite.contains_of_flat_surjective` : the target of a flat surjective
  morphism whose source is contained in a big fppf site is contained in it. This is the size
  obligation in isolation.
* `AlgebraicGeometry.BigFppfOver.exists_descent_of_exists_descent_scheme` : a descent of the
  object `V` along `f` by a bare scheme upgrades to one by an object of the site.
* `AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_isEffectiveFpqcDescent_scheme` : Stacks
  0APL with a hypothesis whose conclusion mentions only schemes. **This is Stacks 0APK and
  nothing else**: the size obligation beside it is discharged here.

## Implementation notes

The size bound is `AlgebraicGeometry.Scheme.size_lt_of_flat_of_surjective_of_isStrongPrelimit`
instantiated at `BigFppfSite.cutoff_isStrongPrelimit`, which is a field of
`AlgebraicGeometry.BigFppfSite`. No regularity or cofinality assumption on the cutoff is used;
in particular `Cardinal.IsRegular` is never invoked, since a cutoff that is both a strong
prelimit and regular would be inaccessible and the construction of the site does not supply
one.

Transporting the descent from schemes to the site has three steps. The underlying scheme of the
descended object is the bare scheme itself, with structure morphism obtained by composing with
that of `T`; `AlgebraicGeometry.BigFppfOver.toScheme` preserves fibre products, so the fibre
product of `f` with the new object maps isomorphically onto the scheme-level fibre product, and
composing with the given isomorphism gives an isomorphism of schemes over `T'`. Being over `T'`
it lifts to the slice, because the canonical functor to schemes is faithful and the inclusion of
the size-bounded subcategory is fully faithful. The cocycle equation is transported through the
fibre product of the second projection with itself, again using preservation of fibre products.

## References

* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace BigFppfSite

/-- The target of a flat surjective morphism of schemes whose source is contained in a big fppf
site is itself contained in that site: the cutoff is a strong prelimit cardinal, and the size of
the target is bounded by a double exponential of the size of the source. -/
theorem contains_of_flat_surjective (B : BigFppfSite.{u}) {V W : Scheme.{u}} (g : V ⟶ W)
    [Flat g] [Surjective g] (hV : B.Contains V) : B.Contains W :=
  Scheme.size_lt_of_flat_of_surjective_of_isStrongPrelimit B.cutoff_isStrongPrelimit g hV

end BigFppfSite

/-- A functor preserving the kernel pair of `k` carries an equation coequalizing the kernel pair
of `m` to the kernel pair of `k`, along an isomorphism `F.obj P ≅ P'` over `m`. -/
theorem map_pullback_fst_comp_eq_map_pullback_snd_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {P W : C} (k : P ⟶ W) [HasPullback k k] [PreservesLimit (cospan k k) F]
    {P' Z : D} {m : P' ⟶ F.obj W} [HasPullback m m] (e : F.obj P ≅ P')
    (hek : e.hom ≫ m = F.map k) (φ : P' ⟶ Z)
    (h : pullback.fst m m ≫ φ = pullback.snd m m ≫ φ) :
    F.map (pullback.fst k k) ≫ e.hom ≫ φ = F.map (pullback.snd k k) ≫ e.hom ≫ φ := by
  have hmm : IsPullback (F.map (pullback.fst k k) ≫ e.hom) (F.map (pullback.snd k k) ≫ e.hom)
      m m :=
    ((IsPullback.of_hasPullback k k).map F).of_iso (Iso.refl _) e e (Iso.refl _) (by simp)
      (by simp) (by simpa using hek.symm) (by simpa using hek.symm)
  rw [← reassoc_of% hmm.isoPullback_hom_fst, ← reassoc_of% hmm.isoPullback_hom_snd, h]

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace BigFppfOver

/-- A scheme whose base change along a flat surjective morphism of the site is isomorphic to an
object of the site is itself contained in the site. -/
theorem contains_of_iso_pullback {T T' V : BigFppfOver B S hS} (f : T' ⟶ T)
    (hfs : Surjective ((BigFppfOver.toScheme B S hS).map f))
    (hff : Flat ((BigFppfOver.toScheme B S hS).map f))
    {W₀ : Scheme.{u}} {w₀ : W₀ ⟶ (BigFppfOver.toScheme B S hS).obj T}
    (α₀ : pullback ((BigFppfOver.toScheme B S hS).map f) w₀ ≅
      (BigFppfOver.toScheme B S hS).obj V) :
    B.Contains W₀ := by
  have := hfs
  have := hff
  exact B.contains_of_flat_surjective
    (α₀.inv ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map f) w₀) V.left.property

/-- **The size obligation of Stacks 0APL, discharged.** If the descent datum of `V` along the
flat surjective morphism `f` of the site is effective as a datum of *schemes* — that is, there
is a scheme `W₀` over the underlying scheme of `T` whose base change along `f` is `V`,
compatibly with `p` and with the cocycle equation for `q` — then it is effective inside the
site: `W₀` carries the structure of an object of the big fppf category over `S` for which the
fibre product with `f` is `V` in the site. -/
theorem exists_descent_of_exists_descent_scheme {T T' U V : BigFppfOver B S hS} (f : T' ⟶ T)
    (hfs : Surjective ((BigFppfOver.toScheme B S hS).map f))
    (hff : Flat ((BigFppfOver.toScheme B S hS).map f))
    (q : V ⟶ U) (p : V ⟶ T')
    (h : ∃ (W₀ : Scheme.{u}) (w₀ : W₀ ⟶ (BigFppfOver.toScheme B S hS).obj T)
      (α₀ : pullback ((BigFppfOver.toScheme B S hS).map f) w₀ ≅
        (BigFppfOver.toScheme B S hS).obj V),
      α₀.hom ≫ (BigFppfOver.toScheme B S hS).map p =
          pullback.fst ((BigFppfOver.toScheme B S hS).map f) w₀ ∧
        pullback.fst (pullback.snd ((BigFppfOver.toScheme B S hS).map f) w₀)
              (pullback.snd ((BigFppfOver.toScheme B S hS).map f) w₀) ≫
            α₀.hom ≫ (BigFppfOver.toScheme B S hS).map q =
          pullback.snd (pullback.snd ((BigFppfOver.toScheme B S hS).map f) w₀)
              (pullback.snd ((BigFppfOver.toScheme B S hS).map f) w₀) ≫
            α₀.hom ≫ (BigFppfOver.toScheme B S hS).map q) :
    ∃ (W : BigFppfOver B S hS) (w : W ⟶ T) (α : pullback f w ≅ V),
      α.hom ≫ p = pullback.fst f w ∧
        pullback.fst (pullback.snd f w) (pullback.snd f w) ≫ α.hom ≫ q =
          pullback.snd (pullback.snd f w) (pullback.snd f w) ≫ α.hom ≫ q := by
  obtain ⟨W₀, w₀, α₀, hα₀, hcoc⟩ := h
  have hW₀ : B.Contains W₀ := contains_of_iso_pullback f hfs hff α₀
  let w₀' : B.obj hW₀ ⟶ T.left := B.inclusion.preimage w₀
  let W : BigFppfOver B S hS := Over.mk (w₀' ≫ T.hom)
  let w : W ⟶ T := Over.homMk w₀'
  have hwmap : (BigFppfOver.toScheme B S hS).map w = w₀ :=
    B.inclusion.map_preimage (X := B.obj hW₀) (Y := T.left) w₀
  have hPB : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst f w))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd f w))
      ((BigFppfOver.toScheme B S hS).map f) w₀ := by
    rw [← hwmap]
    exact (IsPullback.of_hasPullback f w).map (BigFppfOver.toScheme B S hS)
  let e : (BigFppfOver.toScheme B S hS).obj (pullback f w) ≅
      pullback ((BigFppfOver.toScheme B S hS).map f) w₀ := hPB.isoPullback
  let β : (BigFppfOver.toScheme B S hS).obj (pullback f w) ≅
      (BigFppfOver.toScheme B S hS).obj V := e ≪≫ α₀
  have hβeq : β.hom = e.hom ≫ α₀.hom := rfl
  have hβ : β.hom ≫ (BigFppfOver.toScheme B S hS).map p =
      (BigFppfOver.toScheme B S hS).map (pullback.fst f w) := by
    rw [hβeq, Category.assoc, hα₀]
    exact hPB.isoPullback_hom_fst
  let βS : (pullback f w).left ≅ V.left := B.inclusion.preimageIso β
  have hβS : B.inclusion.map βS.hom = β.hom := B.inclusion.map_preimage _
  have hleft : βS.hom ≫ p.left = (pullback.fst f w).left :=
    B.inclusion.map_injective (by rwa [Functor.map_comp, hβS])
  let α : pullback f w ≅ V := Over.isoMk βS (by
    rw [← Over.w p, ← Category.assoc, hleft, Over.w])
  have hαmap : (BigFppfOver.toScheme B S hS).map α.hom = β.hom := hβS
  refine ⟨W, w, α, (BigFppfOver.toScheme B S hS).map_injective ?_, ?_⟩
  · rwa [Functor.map_comp, hαmap]
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp, hαmap, hβeq]
  simp only [Category.assoc]
  exact map_pullback_fst_comp_eq_map_pullback_snd_comp (BigFppfOver.toScheme B S hS)
    (pullback.snd f w) e hPB.isoPullback_hom_snd _ hcoc

end BigFppfOver

namespace IsAlgebraicSpace

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0APL with Stacks 0APK as its only hypothesis.** An algebraic space over `S` is a
sheaf for the fpqc topology of the big fppf category over `S` as soon as each of the descent
data which the middle paragraph of the source constructs, along an fpqc covering consisting of a
single surjective flat quasi-compact morphism of the site, is effective **as a datum of
schemes** — the descended object is a bare scheme, with no size condition.

This is
`AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_isEffectiveFpqcDescent` with its size
obligation discharged by
`AlgebraicGeometry.BigFppfOver.exists_descent_of_exists_descent_scheme`. It proves no new
mathematics; it records, machine-checkably, that the residue of Stacks 0APL is Stacks 0APK and
nothing else. Nothing here needs `B.cutoff.IsRegular`, and no regularity or cofinality
hypothesis on the cutoff is introduced.

Both ends of `f` are demanded affine, which the first paragraph of the source delivers; the
hypothesis is therefore the case of Stacks 0APK that the proof of that tag reduces to by
Stacks 02W3, so Stacks 02W3 lies off the route from here to Stacks 0APL. See the implementation
notes of `StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SeparatedAtlas`. -/
theorem isSheaf_fpqc_of_isEffectiveFpqcDescent_scheme (hF : IsAlgebraicSpace B S hS F)
    (hAPK : ∀ (T T' : BigFppfOver B S hS) (f : T' ⟶ T),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj T') →
      Surjective ((BigFppfOver.toScheme B S hS).map f) →
      Flat ((BigFppfOver.toScheme B S hS).map f) →
      QuasiCompact ((BigFppfOver.toScheme B S hS).map f) →
      ∀ (U V : BigFppfOver B S hS) (u : yoneda.obj U ⟶ F) (q : V ⟶ U) (p : V ⟶ T')
      (c : yoneda.obj T' ⟶ F), IsPullback (yoneda.map q) (yoneda.map p) u c →
      Surjective ((BigFppfOver.toScheme B S hS).map p) →
      Etale ((BigFppfOver.toScheme B S hS).map p) →
      _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map p) →
      IsIndQuasiAffineHom ((BigFppfOver.toScheme B S hS).map p) →
      yoneda.map (pullback.fst f f) ≫ c = yoneda.map (pullback.snd f f) ≫ c →
      ∃ (W₀ : Scheme.{u}) (w₀ : W₀ ⟶ (BigFppfOver.toScheme B S hS).obj T)
        (α₀ : pullback ((BigFppfOver.toScheme B S hS).map f) w₀ ≅
          (BigFppfOver.toScheme B S hS).obj V),
        α₀.hom ≫ (BigFppfOver.toScheme B S hS).map p =
            pullback.fst ((BigFppfOver.toScheme B S hS).map f) w₀ ∧
          pullback.fst (pullback.snd ((BigFppfOver.toScheme B S hS).map f) w₀)
                (pullback.snd ((BigFppfOver.toScheme B S hS).map f) w₀) ≫
              α₀.hom ≫ (BigFppfOver.toScheme B S hS).map q =
            pullback.snd (pullback.snd ((BigFppfOver.toScheme B S hS).map f) w₀)
                (pullback.snd ((BigFppfOver.toScheme B S hS).map f) w₀) ≫
              α₀.hom ≫ (BigFppfOver.toScheme B S hS).map q) :
    Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck) F :=
  hF.isSheaf_fpqc_of_isEffectiveFpqcDescent fun T T' f hTaff hT'aff hfs hff hfqc U V u q p c sq
    hp hpe hpsep hpiqa hcc =>
      BigFppfOver.exists_descent_of_exists_descent_scheme f hfs hff q p
        (hAPK T T' f hTaff hT'aff hfs hff hfqc U V u q p c sq hp hpe hpsep hpiqa hcc)

end IsAlgebraicSpace

end AlgebraicGeometry

end
