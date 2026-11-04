module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyAutomorphisms
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverField
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalarsCartesian
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeSpectrumComparisonIso
public import StacksFrontier.AlgebraicGeometry.GroupScheme.UnramifiedInfinitesimalAutomorphisms
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectOverField
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Defs
public import StacksFrontier.Deformation.Examples.Geometric.CurvesDeformationComparison
public import StacksFrontier.Deformation.Examples.Geometric.SchemesInfinitesimalAutomorphismsTrivial
public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationFiberAut
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Infinitesimal automorphisms of a curve as sections of its automorphism functor

Let `X` be a proper scheme of dimension at most one over a field `k`, and `Aut(X)` the
automorphism functor of the family of curves `X ⟶ Spec k`
(`AlgebraicGeometry.CurveFamily.autFunctor`). Its sections over `Spec k[ε]` lying over the
structure morphism `Spec k[ε] ⟶ Spec k` and restricting to the identity over `Spec k` are the
self-maps of `X ×_{Spec k} Spec k[ε]` over `Spec k[ε]` which fix the special fibre `X`. This is
the identification the proof of Stacks 0E6G makes between tangent vectors of `Aut(X)` at the
identity and infinitesimal automorphisms of `X`.

The scheme `Spec k[ε]` lies in every big fppf site containing `Spec k`: it is of finite type over
`Spec k`, so its size is bounded by that of `Spec k` (Stacks 000R (5)).

## Main definitions

* `AlgebraicGeometry.dualNumberSiteObject`: `Spec k[ε]` as a scheme of the site.
* `AlgebraicGeometry.CurveFamily.autFunctorDualNumberSectionsEquiv`: the sections of `Aut(X)` over
  `Spec k[ε]` over the structure morphism and restricting to the identity are the self-maps of the
  trivial deformation `X ×_{Spec k} Spec k[ε]` over `Spec k[ε]` fixing `X`.

## References

* [Stacks Project, Tag 0E6G](https://stacks.math.columbia.edu/tag/0E6G)
* [Stacks Project, Tag 05Y1](https://stacks.math.columbia.edu/tag/05Y1)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]

/-- **Conjugation by an isomorphism identifies self-maps over a base fixing a subobject.** Let
`φ : Y ≅ Y'` carry `f : Y ⟶ T` to `f' : Y' ⟶ T'` and `s : E ⟶ Y` to `s' : E' ⟶ Y'` up to
isomorphisms of `T` and `E`. Then the automorphisms of `Y` over `T` restricting to the identity
along `s` correspond to those of `Y'` over `T'` restricting to the identity along `s'`. -/
def isoSelfMapsEquivOfIso {Y Y' T T' E E' : C} {f : Y ⟶ T} {s : E ⟶ Y} {f' : Y' ⟶ T'}
    {s' : E' ⟶ Y'} (φ : Y ≅ Y') (ψ : T ≅ T') (χ : E ≅ E') (hf : φ.hom ≫ f' = f ≫ ψ.hom)
    (hs : χ.hom ≫ s' = s ≫ φ.hom) :
    { e : Y ⟶ Y // IsIso e ∧ e ≫ f = f ∧ s ≫ e = s } ≃
      { e : Y' ⟶ Y' // IsIso e ∧ e ≫ f' = f' ∧ s' ≫ e = s' } where
  toFun e :=
    ⟨φ.inv ≫ e.1 ≫ φ.hom, by have := e.2.1; infer_instance, by
      have hf' : f' = φ.inv ≫ f ≫ ψ.hom := by rw [← hf, Iso.inv_hom_id_assoc]
      rw [Category.assoc, Category.assoc, hf, reassoc_of% e.2.2.1, ← hf'], by
      have hs' : s' = χ.inv ≫ s ≫ φ.hom := by rw [← hs, Iso.inv_hom_id_assoc]
      rw [hs', Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% e.2.2.2]⟩
  invFun e :=
    ⟨φ.hom ≫ e.1 ≫ φ.inv, by have := e.2.1; infer_instance, by
      have hf' : f = φ.hom ≫ f' ≫ ψ.inv := by rw [reassoc_of% hf, Iso.hom_inv_id, Category.comp_id]
      rw [Category.assoc, Category.assoc, hf', Iso.inv_hom_id_assoc, reassoc_of% e.2.2.1], by
      have hs' : s = χ.hom ≫ s' ≫ φ.inv := by rw [reassoc_of% hs, Iso.hom_inv_id, Category.comp_id]
      rw [hs', Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% e.2.2.2]⟩
  left_inv e := Subtype.ext (by simp)
  right_inv e := Subtype.ext (by simp)

/-- **A fully faithful functor identifies self-maps over a base fixing a subobject.** The
automorphisms of `Y` over `T` restricting to the identity along `s` correspond to the
automorphisms of `G Y` over `G T` restricting to the identity along `G s`. -/
def isoSelfMapsEquivOfFullyFaithful {G : C ⥤ D} (hG : G.FullyFaithful) {Y T E : C}
    (f : Y ⟶ T) (s : E ⟶ Y) :
    { e : Y ⟶ Y // IsIso e ∧ e ≫ f = f ∧ s ≫ e = s } ≃
      { e : G.obj Y ⟶ G.obj Y // IsIso e ∧ e ≫ G.map f = G.map f ∧ G.map s ≫ e = G.map s } where
  toFun e :=
    ⟨G.map e.1, by have := e.2.1; infer_instance, by rw [← G.map_comp, e.2.2.1],
      by rw [← G.map_comp, e.2.2.2]⟩
  invFun e :=
    ⟨hG.preimage e.1, by
      have := e.2.1
      exact (hG.preimageIso (asIso e.1)).isIso_hom, hG.map_injective (by
        rw [G.map_comp, hG.map_preimage, e.2.2.1]), hG.map_injective (by
        rw [G.map_comp, hG.map_preimage, e.2.2.2])⟩
  left_inv e := Subtype.ext (hG.preimage_map e.1)
  right_inv e := Subtype.ext (hG.map_preimage e.1)

end CategoryTheory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z X Q T T₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}

/-- **The pairs of Stacks 05Y1 with a given first component** `b : T ⟶ Q` are the morphisms
`T ×_{b, Q} Z ⟶ X` lying over `Q`, compatibly with any condition on the pairs. -/
def RelativeMorphism.baseEqEquiv (b : T ⟶ Q) (R : RelativeMorphism B S hS Z X Q z x T → Prop) :
    { p : RelativeMorphism B S hS Z X Q z x T // p.base = b ∧ R p } ≃
      { m : { m : pullback b z ⟶ X // m ≫ x = pullback.snd b z ≫ z } //
        R ⟨b, m.1, m.2⟩ } where
  toFun p :=
    ⟨⟨(pullback.congrHom p.2.1.symm rfl).hom ≫ p.1.morphism, by
        rw [Category.assoc, p.1.commutes, ← Category.assoc, pullback.congrHom_hom_snd]⟩, by
      have h : (⟨b, (pullback.congrHom p.2.1.symm rfl).hom ≫ p.1.morphism, by
          rw [Category.assoc, p.1.commutes, ← Category.assoc, pullback.congrHom_hom_snd]⟩ :
            RelativeMorphism B S hS Z X Q z x T) = p.1 :=
        RelativeMorphism.ext_of_base_eq p.2.1.symm rfl
      rw [h]
      exact p.2.2⟩
  invFun m := ⟨⟨b, m.1.1, m.1.2⟩, rfl, m.2⟩
  left_inv p := Subtype.ext (RelativeMorphism.ext_of_base_eq p.2.1.symm rfl)
  right_inv m := by
    refine Subtype.ext (Subtype.ext ?_)
    have hid : (pullback.congrHom (rfl : b = b) (rfl : z = z)).hom = 𝟙 (pullback b z) :=
      pullback.hom_ext (by rw [pullback.congrHom_hom_fst, Category.id_comp])
        (by rw [pullback.congrHom_hom_snd, Category.id_comp])
    change (pullback.congrHom (rfl : b = b) (rfl : z = z)).hom ≫ m.1.1 = m.1.1
    rw [hid, Category.id_comp]

/-- A pair `(b, m)` restricts along `t : T₀ ⟶ T` to the identity pair exactly when `m` restricted
to `T₀ ×_{t ≫ b, Q} Z` is the projection to `Z`. -/
theorem RelativeMorphism.restrict_mk_eq_identity_iff (b : T ⟶ Q) (t : T₀ ⟶ T)
    (m : pullback b z ⟶ Z) (hm : m ≫ z = pullback.snd b z ≫ z) :
    RelativeMorphism.restrict t (⟨b, m, hm⟩ : RelativeMorphism B S hS Z Z Q z z T) =
        RelativeMorphism.identity z (t ≫ b) ↔
      pullback.mapFst t b z ≫ m = pullback.snd (t ≫ b) z := by
  show RelativeMorphism.mk (t ≫ b)
      (pullback.map (t ≫ b) z b z t (𝟙 Z) (𝟙 Q) (by simp) (by simp) ≫ m) _ =
    RelativeMorphism.mk (t ≫ b) (pullback.snd (t ≫ b) z) rfl ↔ _
  refine ⟨fun h => ?_, fun h => RelativeMorphism.mk_eq_mk (by rwa [pullback.map_id_eq_mapFst])⟩
  have h' := eq_of_heq (RelativeMorphism.mk.inj h).2
  rwa [pullback.map_id_eq_mapFst] at h'

/-- **The relative automorphisms with a given first component restricting to the identity are
the automorphisms of the base change fixing the restricted base change.** For `b : T ⟶ Q` and
`t : T₀ ⟶ T`, the pairs of Stacks 05Y1 for `z : Z ⟶ Q` against itself with first component `b`
which are relative isomorphisms and restrict along `t` to the identity pair are the
automorphisms of `T ×_{b, Q} Z` over `T` restricting to the identity of `T₀ ×_{t ≫ b, Q} Z`. -/
def relativeMorphismEquivIsoSelfMaps (b : T ⟶ Q) (t : T₀ ⟶ T) :
    { p : RelativeMorphism B S hS Z Z Q z z T //
        p.base = b ∧ p.IsRelativeIso ∧
          RelativeMorphism.restrict t p = RelativeMorphism.identity z (t ≫ b) } ≃
      { e : pullback b z ⟶ pullback b z // IsIso e ∧
          e ≫ pullback.fst b z = pullback.fst b z ∧
          pullback.mapFst t b z ≫ e = pullback.mapFst t b z } :=
  (RelativeMorphism.baseEqEquiv b
      (fun p => p.IsRelativeIso ∧
        RelativeMorphism.restrict t p = RelativeMorphism.identity z (t ≫ b))).trans
    { toFun m :=
        ⟨pullback.lift (pullback.fst b z) m.1.1 (by rw [m.1.2, pullback.condition]),
          m.2.1, pullback.lift_fst _ _ _, by
          refine pullback.hom_ext ?_ ?_
          · rw [Category.assoc, pullback.lift_fst]
          · rw [Category.assoc, pullback.lift_snd, pullback.mapFst_snd,
              (RelativeMorphism.restrict_mk_eq_identity_iff b t m.1.1 m.1.2).1 m.2.2]⟩
      invFun e :=
        ⟨⟨e.1 ≫ pullback.snd b z, by
            rw [Category.assoc, ← pullback.condition, ← Category.assoc, e.2.2.1,
              pullback.condition]⟩, by
          have he : pullback.lift (pullback.fst b z) (e.1 ≫ pullback.snd b z) (by
              rw [Category.assoc, ← pullback.condition, ← Category.assoc, e.2.2.1]) = e.1 :=
            pullback.hom_ext (by rw [pullback.lift_fst, e.2.2.1]) (by rw [pullback.lift_snd])
          refine ⟨?_, ?_⟩
          · change IsIso (pullback.lift (pullback.fst b z) (e.1 ≫ pullback.snd b z) _)
            rw [he]
            exact e.2.1
          · refine (RelativeMorphism.restrict_mk_eq_identity_iff b t _ _).2 ?_
            rw [← Category.assoc, e.2.2.2, pullback.mapFst_snd]⟩
      left_inv m := Subtype.ext (Subtype.ext (pullback.lift_snd _ _ _))
      right_inv e := Subtype.ext
        (pullback.hom_ext (by rw [pullback.lift_fst, e.2.2.1]) (by rw [pullback.lift_snd])) }

section Representable

variable {W V T T₀ : BigFppfOver B S hS}

/-- **On representable presheaves the automorphisms of the base change are those of the base
change of schemes.** For morphisms `a : T ⟶ V`, `w : W ⟶ V` and `ι : T₀ ⟶ T` of the site, the
automorphisms of `T ×_V W` over `T` restricting to the identity of `T₀ ×_V W` correspond, through
the Yoneda embedding, to those of the fibre product of the representable presheaves. -/
def yonedaIsoSelfMapsEquiv (w : W ⟶ V) (a : T ⟶ V) (ι : T₀ ⟶ T) :
    { e : pullback (yoneda.map a) (yoneda.map w) ⟶ pullback (yoneda.map a) (yoneda.map w) //
        IsIso e ∧ e ≫ pullback.fst (yoneda.map a) (yoneda.map w) =
          pullback.fst (yoneda.map a) (yoneda.map w) ∧
        pullback.mapFst (yoneda.map ι) (yoneda.map a) (yoneda.map w) ≫ e =
          pullback.mapFst (yoneda.map ι) (yoneda.map a) (yoneda.map w) } ≃
      { e : pullback a w ⟶ pullback a w // IsIso e ∧ e ≫ pullback.fst a w = pullback.fst a w ∧
          pullback.mapFst ι a w ≫ e = pullback.mapFst ι a w } :=
  (isoSelfMapsEquivOfIso (PreservesPullback.iso yoneda a w) (Iso.refl _)
      (PreservesPullback.iso yoneda (ι ≫ a) w ≪≫
        pullback.congrHom (yoneda.map_comp ι a) rfl)
      (by rw [PreservesPullback.iso_hom_fst, Iso.refl_hom, Category.comp_id])
      (by
        refine pullback.hom_ext ?_ ?_
        · simp only [Iso.trans_hom, Category.assoc, pullback.mapFst_fst,
            pullback.congrHom_hom_fst_assoc, PreservesPullback.iso_hom_fst_assoc,
            PreservesPullback.iso_hom_fst, ← Functor.map_comp]
        · simp only [Iso.trans_hom, Category.assoc, pullback.mapFst_snd,
            pullback.congrHom_hom_snd, PreservesPullback.iso_hom_snd,
            ← Functor.map_comp])).symm.trans
    (isoSelfMapsEquivOfFullyFaithful Yoneda.fullyFaithful _ _).symm

/-- **The sections of `Isom_V(W, W)` over `T` with a given projection restricting to the identity
along `ι`** are the automorphisms of the fibre product `T ×_V W` over `T` restricting to the
identity of `T₀ ×_V W`. Here `Isom_V(W, W)` is the subfunctor of relative isomorphisms
(Stacks 0DPP) of the relative morphism functor (Stacks 05Y2) of a morphism `w : W ⟶ V` of the
site, read on representable presheaves. -/
def isomSubfunctorYonedaSectionsEquiv (w : W ⟶ V) (a : T ⟶ V) (ι : T₀ ⟶ T)
    (hW : IsAlgebraicSpace B S hS (yoneda.obj W)) (hV : IsAlgebraicSpace B S hS (yoneda.obj V)) :
    { s : (isomSubfunctor B S hS (yoneda.obj W) (yoneda.obj W) (yoneda.obj V) (yoneda.map w)
          (yoneda.map w) hW hW hV).toFunctor.obj (op T) //
        (relativeHomProjection B S hS (yoneda.obj W) (yoneda.obj W) (yoneda.obj V) (yoneda.map w)
            (yoneda.map w) hW hW hV).app (op T) s.1 = a ∧
          relativeHomSections B S hS (yoneda.obj W) (yoneda.obj W) (yoneda.obj V) (yoneda.map w)
              (yoneda.map w) hW hW hV T₀
              ((isomSubfunctor B S hS (yoneda.obj W) (yoneda.obj W) (yoneda.obj V) (yoneda.map w)
                (yoneda.map w) hW hW hV).toFunctor.map ι.op s).1 =
            RelativeMorphism.identity (yoneda.map w) (yoneda.map (ι ≫ a)) } ≃
      { e : pullback a w ⟶ pullback a w // IsIso e ∧ e ≫ pullback.fst a w = pullback.fst a w ∧
          pullback.mapFst ι a w ≫ e = pullback.mapFst ι a w } :=
  let H := relativeHomSections B S hS (yoneda.obj W) (yoneda.obj W) (yoneda.obj V) (yoneda.map w)
    (yoneda.map w) hW hW hV
  have hbase : ∀ p : RelativeMorphism B S hS (yoneda.obj W) (yoneda.obj W) (yoneda.obj V)
      (yoneda.map w) (yoneda.map w) (yoneda.obj T), yonedaEquiv p.base = a ↔
        p.base = yoneda.map a := fun p => by
    rw [← yonedaEquiv_yoneda_map a]
    exact yonedaEquiv.injective.eq_iff
  (({ toFun s := ⟨H T s.1.1, (hbase _).1 s.2.1, s.1.2, by
          rw [← Functor.map_comp, ← relativeHomSections_map]
          exact s.2.2⟩
      invFun p := ⟨⟨(H T).symm p.1, by
          change (H T ((H T).symm p.1)).IsRelativeIso
          rw [Equiv.apply_symm_apply]
          exact p.2.2.1⟩, by
          refine ⟨?_, ?_⟩
          · change yonedaEquiv (H T ((H T).symm p.1)).base = a
            rw [Equiv.apply_symm_apply, p.2.1, yonedaEquiv_yoneda_map]
          · change H T₀ ((relativeHom B S hS (yoneda.obj W) (yoneda.obj W) (yoneda.obj V)
              (yoneda.map w) (yoneda.map w) hW hW hV).map ι.op ((H T).symm p.1)) = _
            rw [relativeHomSections_map, Equiv.apply_symm_apply, p.2.2.2, Functor.map_comp]⟩
      left_inv s := Subtype.ext (Subtype.ext ((H T).symm_apply_apply _))
      right_inv p := Subtype.ext ((H T).apply_symm_apply _) } :
      { s : (isomSubfunctor B S hS (yoneda.obj W) (yoneda.obj W) (yoneda.obj V) (yoneda.map w)
          (yoneda.map w) hW hW hV).toFunctor.obj (op T) //
        (relativeHomProjection B S hS (yoneda.obj W) (yoneda.obj W) (yoneda.obj V) (yoneda.map w)
            (yoneda.map w) hW hW hV).app (op T) s.1 = a ∧
          H T₀ ((isomSubfunctor B S hS (yoneda.obj W) (yoneda.obj W) (yoneda.obj V)
            (yoneda.map w) (yoneda.map w) hW hW hV).toFunctor.map ι.op s).1 =
            RelativeMorphism.identity (yoneda.map w) (yoneda.map (ι ≫ a)) } ≃
      { p : RelativeMorphism B S hS (yoneda.obj W) (yoneda.obj W) (yoneda.obj V) (yoneda.map w)
          (yoneda.map w) (yoneda.obj T) //
        p.base = yoneda.map a ∧ p.IsRelativeIso ∧
          RelativeMorphism.restrict (yoneda.map ι) p =
            RelativeMorphism.identity (yoneda.map w) (yoneda.map ι ≫ yoneda.map a) }).trans
    (relativeMorphismEquivIsoSelfMaps (yoneda.map a) (yoneda.map ι))).trans
    (yonedaIsoSelfMapsEquiv w a ι)

end Representable

end AlgebraicGeometry.Space

namespace AlgebraicGeometry

open Deformation Deformation.Examples

variable {k : Type u} [Field k]

/-- **`Spec k[ε]` lies in every big fppf site containing `Spec k`.** The structure morphism
`Spec k[ε] ⟶ Spec k` is of finite type, so the size of `Spec k[ε]` is bounded by that of
`Spec k` (Stacks 000R (5)). -/
theorem BigFppfSite.contains_spec_dualNumber (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k))) : B.Contains (Spec (.of (DualNumber k))) := by
  have := finitePresentation_dualNumber k
  have : LocallyOfFiniteType (dualNumberToBase k) :=
    locallyOfFiniteType_specMap_algebraMap k (DualNumber k)
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (dualNumberToBase k) hk

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase) (hk : B.Contains (Spec (.of k)))

/-- `Spec k[ε]`, as a scheme of the big fppf site over the integers. -/
abbrev dualNumberSiteObject : BigFppfOver B integerBase hZ :=
  integerSiteObject B hZ (BigFppfSite.contains_spec_dualNumber B hk)

/-- The structure morphism `Spec k[ε] ⟶ Spec k`, as a morphism of the site. -/
abbrev dualNumberSiteMap : dualNumberSiteObject B hZ hk ⟶ integerSiteObject B hZ hk :=
  integerSiteMap B hZ _ hk (dualNumberToBase k)

/-- The closed point `Spec k ⟶ Spec k[ε]`, as a morphism of the site. -/
abbrev dualNumberClosedPointSiteMap : integerSiteObject B hZ hk ⟶ dualNumberSiteObject B hZ hk :=
  integerSiteMap B hZ hk _ (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k)))

/-- The closed point of `Spec k[ε]` is a section of its structure morphism. -/
theorem dualNumberClosedPointSiteMap_comp_dualNumberSiteMap :
    dualNumberClosedPointSiteMap B hZ hk ≫ dualNumberSiteMap B hZ hk = 𝟙 _ := by
  rw [integerSiteMap_comp, ← integerSiteMap_id]
  congr 1
  rw [dualNumberToBase, ← Spec.map_comp, ← Spec.map_id]
  congr 1

/-! ### The trivial deformation as a fibre product of schemes of the site -/

variable (k) in
/-- The spectrum of the dual numbers is the spectrum of the dual-number object of `𝒞_k`. -/
def dualNumberSpecIso :
    Spec (.of (DualNumber k)) ≅ baseSpec (artinianDualNumbers.{u, u, u} k k) :=
  Scheme.Spec.mapIso (dualNumbersEquiv.{u, u, u} (Λ := k) (k := k)).toRingEquiv.toCommRingCatIso.op

variable (k) in
/-- The structure morphism of `Spec k[ε]` is the inclusion `k ⟶ k[ε]` of `𝒞_k`, read on spectra
through the identification of `Spec k` with the spectrum of the residue-field object. -/
theorem dualNumberToBase_comp_residueSpecMap :
    dualNumberToBase k ≫ residueSpecMap (residueFieldObject.{u, u, u} k k) =
      (dualNumberSpecIso k).hom ≫
        baseSpecMap (dualNumbersInclusion.{u, u, u} (Λ := k) (k := k)) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext c
  · show Artin.residueMap (residueFieldObject.{u, u, u} k k) c =
      TrivSqZeroExt.fst (dualNumbersEquiv.{u, u, u} (Λ := k) (k := k)
        ((dualNumbersInclusion.{u, u, u} (Λ := k) (k := k)).hom c))
    rw [dualNumbersEquiv_fst]
    exact residueFieldObject_residue k k c
  · show (0 : k) = TrivSqZeroExt.snd (dualNumbersEquiv.{u, u, u} (Λ := k)
      (dualNumbersUp.{u, u, u} (Λ := k) (TrivSqZeroExt.inl (ULift.down c))))
    rw [show dualNumbersEquiv.{u, u, u} (Λ := k)
        (dualNumbersUp.{u, u, u} (Λ := k) (TrivSqZeroExt.inl (ULift.down c))) =
          TrivSqZeroExt.inl (ULift.down c) from
      (AlgEquiv.ofBijective _ dualNumbersUp_bijective.{u, u, u}).symm_apply_apply _]
    rfl

variable (k) in
/-- The closed point of the dual-number object of `𝒞_k` is the closed point of `Spec k[ε]`. -/
theorem residueSpecMap_artinianDualNumbers :
    residueSpecMap (artinianDualNumbers.{u, u, u} k k) =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k)) ≫ (dualNumberSpecIso k).hom := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext z
  show TrivSqZeroExt.fst z = TrivSqZeroExt.fst (dualNumbersEquiv.{u, u, u} (Λ := k) (k := k) z)
  rw [dualNumbersEquiv_fst]

variable (X : Over (Spec (.of k))) [IsProper X.hom]

/-- The structure morphism `X ⟶ Spec k` of a proper scheme over `k`, as a morphism of the site;
`X` lies in the site because it is of finite type over `Spec k` (Stacks 000R (5)). -/
abbrev overFieldSiteMap :
    integerSiteObject B hZ (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk) ⟶
      integerSiteObject B hZ hk :=
  integerSiteMap B hZ _ hk X.hom

/-- **The trivial deformation `X ×_{Spec k} Spec k[ε]` is the fibre product of the site**: the
fibre product of `Spec k[ε] ⟶ Spec k` and `X ⟶ Spec k` in the site is cartesian, as a square
of schemes, over the inclusion `k ⟶ k[ε]` of `𝒞_k`. -/
theorem isPullback_dualNumberSiteMap_overFieldSiteMap :
    IsPullback ((BigFppfOver.toScheme B integerBase hZ).map
        (pullback.fst (dualNumberSiteMap B hZ hk) (overFieldSiteMap B hZ hk X)) ≫
          (dualNumberSpecIso k).hom)
      ((BigFppfOver.toScheme B integerBase hZ).map
        (pullback.snd (dualNumberSiteMap B hZ hk) (overFieldSiteMap B hZ hk X)))
      (baseSpecMap (dualNumbersInclusion.{u, u, u} (Λ := k) (k := k)))
      (X.hom ≫ residueSpecMap (residueFieldObject.{u, u, u} k k)) :=
  ((IsPullback.of_hasPullback (dualNumberSiteMap B hZ hk)
    (overFieldSiteMap B hZ hk X)).map (BigFppfOver.toScheme B integerBase hZ)).of_iso
      (Iso.refl _) (dualNumberSpecIso k) (Iso.refl _)
      (@asIso _ _ _ _ (residueSpecMap (residueFieldObject.{u, u, u} k k))
        (isIso_residueSpecMap_residueFieldObject (Λ := k) (k := k)))
      (Category.id_comp _).symm
      (by rw [Iso.refl_hom, Iso.refl_hom, Category.id_comp, Category.comp_id])
      (dualNumberToBase_comp_residueSpecMap k) (Category.id_comp _).symm

/-- The fibre product of the site of `Spec k[ε] ⟶ Spec k` and `X ⟶ Spec k`, as a scheme, is the
total space `X ×_{Spec k} Spec k[ε]` of the trivial deformation of `X`. -/
def dualNumberSitePullbackIso :
    (BigFppfOver.toScheme B integerBase hZ).obj
        (pullback (dualNumberSiteMap B hZ hk) (overFieldSiteMap B hZ hk X)) ≅
      pullback (X.hom ≫ residueSpecMap (residueFieldObject.{u, u, u} k k))
        (baseSpecMap (dualNumbersInclusion.{u, u, u} (Λ := k) (k := k))) :=
  (isPullback_dualNumberSiteMap_overFieldSiteMap B hZ hk X).flip.isoPullback

/-- The identification with the trivial deformation, followed by its projection to `X`. -/
theorem dualNumberSitePullbackIso_hom_fst :
    (dualNumberSitePullbackIso B hZ hk X).hom ≫
        pullback.fst (X.hom ≫ residueSpecMap (residueFieldObject.{u, u, u} k k))
          (baseSpecMap (dualNumbersInclusion.{u, u, u} (Λ := k) (k := k))) =
      (BigFppfOver.toScheme B integerBase hZ).map
          (pullback.snd (dualNumberSiteMap B hZ hk) (overFieldSiteMap B hZ hk X)) :=
  (isPullback_dualNumberSiteMap_overFieldSiteMap B hZ hk X).flip.isoPullback_hom_fst

/-- The identification with the trivial deformation, followed by its projection to the
spectrum of the dual-number object. -/
theorem dualNumberSitePullbackIso_hom_snd :
    (dualNumberSitePullbackIso B hZ hk X).hom ≫
        pullback.snd (X.hom ≫ residueSpecMap (residueFieldObject.{u, u, u} k k))
          (baseSpecMap (dualNumbersInclusion.{u, u, u} (Λ := k) (k := k))) =
      (BigFppfOver.toScheme B integerBase hZ).map
          (pullback.fst (dualNumberSiteMap B hZ hk) (overFieldSiteMap B hZ hk X)) ≫
        (dualNumberSpecIso k).hom :=
  (isPullback_dualNumberSiteMap_overFieldSiteMap B hZ hk X).flip.isoPullback_hom_snd

/-- The composite of the closed point and the structure morphism of `Spec k[ε]` is invertible,
being the identity. -/
theorem isIso_dualNumberClosedPointSiteMap_comp :
    IsIso (dualNumberClosedPointSiteMap B hZ hk ≫ dualNumberSiteMap B hZ hk) := by
  rw [dualNumberClosedPointSiteMap_comp_dualNumberSiteMap]
  infer_instance

/-- The fibre of `X ×_{Spec k} Spec k[ε]` over the closed point, computed in the site, is `X`:
its projection to `X` is an isomorphism, the closed point being a section of the structure
morphism. -/
def dualNumberSiteClosedFibreIso :
    (BigFppfOver.toScheme B integerBase hZ).obj
        (pullback (dualNumberClosedPointSiteMap B hZ hk ≫ dualNumberSiteMap B hZ hk)
          (overFieldSiteMap B hZ hk X)) ≅ X.left :=
  haveI := isIso_dualNumberClosedPointSiteMap_comp B hZ hk
  (BigFppfOver.toScheme B integerBase hZ).mapIso
    (asIso (pullback.snd (dualNumberClosedPointSiteMap B hZ hk ≫ dualNumberSiteMap B hZ hk)
      (overFieldSiteMap B hZ hk X)))

/-- The fibre over the closed point is the special fibre of the trivial deformation. -/
theorem dualNumberSiteClosedFibreIso_hom_specialMap :
    (dualNumberSiteClosedFibreIso B hZ hk X).hom ≫
        pullback.lift (f := (X.hom ≫ residueSpecMap (residueFieldObject.{u, u, u} k k)))
          (g := (baseSpecMap (dualNumbersInclusion.{u, u, u} (Λ := k) (k := k)))) (𝟙 X.left)
          (X.hom ≫ residueSpecMap (artinianDualNumbers.{u, u, u} k k))
          (by rw [Category.id_comp, Category.assoc, residueSpecMap_naturality]) =
      (BigFppfOver.toScheme B integerBase hZ).map
          (pullback.mapFst (dualNumberClosedPointSiteMap B hZ hk)
            (dualNumberSiteMap B hZ hk) (overFieldSiteMap B hZ hk X)) ≫
        (dualNumberSitePullbackIso B hZ hk X).hom := by
  have hc : (dualNumberSiteClosedFibreIso B hZ hk X).hom ≫ X.hom =
      (BigFppfOver.toScheme B integerBase hZ).map (pullback.fst
        (dualNumberClosedPointSiteMap B hZ hk ≫ dualNumberSiteMap B hZ hk)
        (overFieldSiteMap B hZ hk X)) := by
    have h1 : (BigFppfOver.toScheme B integerBase hZ).map
        (dualNumberClosedPointSiteMap B hZ hk ≫ dualNumberSiteMap B hZ hk) = 𝟙 _ := by
      rw [dualNumberClosedPointSiteMap_comp_dualNumberSiteMap, CategoryTheory.Functor.map_id]
    exact ((BigFppfOver.toScheme B integerBase hZ).map_comp _ _).symm.trans
      ((congrArg (BigFppfOver.toScheme B integerBase hZ).map pullback.condition.symm).trans
        (((BigFppfOver.toScheme B integerBase hZ).map_comp _ _).trans
          ((congrArg (fun m => _ ≫ m) h1).trans (Category.comp_id _))))
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, dualNumberSitePullbackIso_hom_fst, pullback.lift_fst,
      Category.comp_id]
    exact (congrArg (BigFppfOver.toScheme B integerBase hZ).map
      (pullback.mapFst_snd _ _ _)).symm.trans
      ((BigFppfOver.toScheme B integerBase hZ).map_comp _ _)
  · rw [Category.assoc, Category.assoc, dualNumberSitePullbackIso_hom_snd, pullback.lift_snd,
      ← Category.assoc, hc, residueSpecMap_artinianDualNumbers]
    exact (Category.assoc _ _ _).symm.trans <|
      (congrArg (fun m => m ≫ (dualNumberSpecIso k).hom)
        (((BigFppfOver.toScheme B integerBase hZ).map_comp _ _).symm.trans
          ((congrArg (BigFppfOver.toScheme B integerBase hZ).map
              (pullback.mapFst_fst _ _ _).symm).trans
            ((BigFppfOver.toScheme B integerBase hZ).map_comp _ _)))).trans (Category.assoc _ _ _)

namespace CurveFamily

variable (hdim : topologicalKrullDim X.left ≤ 1)

/-- **The tangent vectors of `Aut(X)` at the identity are the infinitesimal automorphisms of `X`.**
Let `X` be a proper scheme of dimension at most one over a field `k`, with automorphism functor
`Aut(X)` (Stacks 0DSW). The sections of `Aut(X)` over `Spec k[ε]` lying over the structure
morphism `Spec k[ε] ⟶ Spec k` and restricting to the identity over the closed point are the
self-maps of the trivial deformation `X ×_{Spec k} Spec k[ε]` over `Spec k[ε]` which restrict to
the identity of `X`. This is the identification made in the proof of Stacks 0E6G. -/
@[sga "3 VIIA 1.5" "special case", sga "3 VIIA 2.5" "special case"]
def autFunctorDualNumberSectionsEquiv :
    { s : (autFunctor (curveFamilyOfScheme X B hZ hk hdim)).toFunctor.obj
          (op (dualNumberSiteObject B hZ hk)) //
        (autFunctorProjection (curveFamilyOfScheme X B hZ hk hdim)).app _ s =
            dualNumberSiteMap B hZ hk ∧
          Space.relativeHomSections B integerBase hZ _ _ _ _ _ _ _ _ (integerSiteObject B hZ hk)
              ((autFunctor (curveFamilyOfScheme X B hZ hk hdim)).toFunctor.map
                (dualNumberClosedPointSiteMap B hZ hk).op s).1 =
            Space.RelativeMorphism.identity _ (𝟙 _) } ≃
      { e : (dualNumbersTrivialDeformation (Λ := k) X).scheme ⟶
          (dualNumbersTrivialDeformation (Λ := k) X).scheme //
        e ≫ (dualNumbersTrivialDeformation (Λ := k) X).toBase =
            (dualNumbersTrivialDeformation (Λ := k) X).toBase ∧
          (dualNumbersTrivialDeformation (Λ := k) X).specialMap ≫ e =
            (dualNumbersTrivialDeformation (Λ := k) X).specialMap } :=
  ((((Equiv.subtypeEquivRight fun _ => and_congr Iff.rfl (by
        rw [dualNumberClosedPointSiteMap_comp_dualNumberSiteMap, yoneda.map_id]
        exact Iff.rfl)).trans
      (Space.isomSubfunctorYonedaSectionsEquiv (overFieldSiteMap B hZ hk X)
        (dualNumberSiteMap B hZ hk) (dualNumberClosedPointSiteMap B hZ hk)
        (isAlgebraicSpace_yoneda B integerBase hZ _)
        (isAlgebraicSpace_yoneda B integerBase hZ _))).trans
    (isoSelfMapsEquivOfFullyFaithful
      (BigFppfOver.fullyFaithfulToScheme B integerBase hZ specULiftZIsTerminal) _ _)).trans
    (isoSelfMapsEquivOfIso (dualNumberSitePullbackIso B hZ hk X) (dualNumberSpecIso k)
      (dualNumberSiteClosedFibreIso B hZ hk X) (dualNumberSitePullbackIso_hom_snd B hZ hk X)
      (dualNumberSiteClosedFibreIso_hom_specialMap B hZ hk X))).trans
    (Equiv.subtypeEquivRight fun e =>
      ⟨fun h => h.2, fun h =>
        ⟨isIso_of_fixes_specialMap_over_base (dualNumbersTrivialDeformation (Λ := k) X) e h.1 h.2,
          h⟩⟩)

open scoped CategoryTheory.MonObj in
/-- **Stacks 0E6G, at a group scheme representing `Aut(X)`.** Let `X` be a proper scheme of
dimension at most one over a field `k`, and `G` a group scheme locally of finite type over `k`
representing the automorphism functor `Aut(X)` over `Spec k`, with unit the identity
automorphism. Then `G` is unramified over `k` if and only if `Der_k(𝒪_X, 𝒪_X) = 0`: the
`k[ε]`-points of `G` over the unit are the infinitesimal automorphisms of `X`
(`AlgebraicGeometry.CurveFamily.autFunctorDualNumberSectionsEquiv`), and these are the
derivations (Stacks 0DY9). -/
theorem unramified_iff_subsingleton_derivations_of_represents (G : Over (Spec (.of k)))
    [GrpObj G] [LocallyOfFiniteType G.hom] (hG : B.Contains G.left)
    (ε : yoneda.obj (integerSiteObject B hZ hG) ≅
      (autFunctor (curveFamilyOfScheme X B hZ hk hdim)).toFunctor)
    (hε : ε.hom ≫ autFunctorProjection (curveFamilyOfScheme X B hZ hk hdim) =
      yoneda.map (integerSiteMap B hZ hG hk G.hom))
    (hη : Space.relativeHomSections B integerBase hZ _ _ _ _ _ _ _ _ (integerSiteObject B hZ hk)
        (ε.hom.app (op (integerSiteObject B hZ hk))
          (integerSiteMap B hZ hk hG (η[G]).left)).1 =
      Space.RelativeMorphism.identity _ (𝟙 _)) :
    Unramified G.hom ↔
      Subsingleton (schemeMorphismDerivations (Λ := k) (k := k) (𝟙 X.left) X.hom) := by
  have hε' := BigFppfSite.contains_spec_dualNumber B hk
  let F := curveFamilyOfScheme X B hZ hk hdim
  let H := Space.relativeHomSections B integerBase hZ F.total.obj F.total.obj
    (schemeSpace F.base).obj F.toBase.hom F.toBase.hom F.total.property F.total.property
    (schemeSpace F.base).property
  have hcomp : ∀ {T₁ T₂ T₃ : Scheme.{u}} {h₁ : B.Contains T₁} {h₂ : B.Contains T₂}
      {h₃ : B.Contains T₃} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) (h : T₁ ⟶ T₃),
      integerSiteMap B hZ h₁ h₂ f ≫ integerSiteMap B hZ h₂ h₃ g = integerSiteMap B hZ h₁ h₃ h ↔
        f ≫ g = h := fun f g h =>
    ⟨fun e => congrArg (BigFppfOver.toScheme B integerBase hZ).map
        ((integerSiteMap_comp _ _).symm.trans e),
      fun e => (integerSiteMap_comp _ _).trans (congrArg _ e)⟩
  have hinj' : Function.Injective fun g : integerSiteObject B hZ hk ⟶ integerSiteObject B hZ hG =>
      H (integerSiteObject B hZ hk) (ε.hom.app (op (integerSiteObject B hZ hk)) g).1 :=
    fun _ _ h => (ε.app (op (integerSiteObject B hZ hk))).toEquiv.injective
      (Subtype.ext ((H _).injective h))
  have hproj : ∀ α : dualNumberSiteObject B hZ hk ⟶ integerSiteObject B hZ hG,
      (autFunctorProjection F).app _ (ε.hom.app (op (dualNumberSiteObject B hZ hk)) α) =
        α ≫ integerSiteMap B hZ hG hk G.hom := fun α =>
    congrArg (fun t => t.app (op (dualNumberSiteObject B hZ hk)) α) hε
  have hres : ∀ α : dualNumberSiteObject B hZ hk ⟶ integerSiteObject B hZ hG,
      (autFunctor F).toFunctor.map (dualNumberClosedPointSiteMap B hZ hk).op
          (ε.hom.app (op (dualNumberSiteObject B hZ hk)) α) =
        ε.hom.app (op (integerSiteObject B hZ hk)) (dualNumberClosedPointSiteMap B hZ hk ≫ α) :=
    fun α => (ConcreteCategory.congr_hom
      (ε.hom.naturality (dualNumberClosedPointSiteMap B hZ hk).op) α).symm
  let e₀ : (Spec (.of (DualNumber k)) ⟶ G.left) ≃
      (dualNumberSiteObject B hZ hk ⟶ integerSiteObject B hZ hG) :=
    { toFun α := integerSiteMap B hZ hε' hG α
      invFun g := (BigFppfOver.toScheme B integerBase hZ).map g
      left_inv _ := rfl
      right_inv g := integerSiteMap_toScheme_map g }
  let φ : { α : Spec (.of (DualNumber k)) ⟶ G.left // α ≫ G.hom = dualNumberToBase k ∧
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k)) ≫ α = (η[G]).left } ≃
      { s : (autFunctor F).toFunctor.obj (op (dualNumberSiteObject B hZ hk)) //
        (autFunctorProjection F).app _ s = dualNumberSiteMap B hZ hk ∧
          H (integerSiteObject B hZ hk)
              ((autFunctor F).toFunctor.map (dualNumberClosedPointSiteMap B hZ hk).op s).1 =
            Space.RelativeMorphism.identity _ (𝟙 _) } :=
    Equiv.subtypeEquiv (e₀.trans (ε.app (op (dualNumberSiteObject B hZ hk))).toEquiv) fun α => by
      show _ ↔ (autFunctorProjection F).app _
          (ε.hom.app (op (dualNumberSiteObject B hZ hk)) (e₀ α)) = _ ∧
        H _ ((autFunctor F).toFunctor.map (dualNumberClosedPointSiteMap B hZ hk).op
          (ε.hom.app (op (dualNumberSiteObject B hZ hk)) (e₀ α))).1 = _
      rw [hproj, hres, ← hη]
      exact and_congr (hcomp _ _ _).symm ((hcomp _ _ _).symm.trans hinj'.eq_iff.symm)
  exact unramified_iff_subsingleton_derivations_of_equiv G
    (dualNumbersTrivialDeformation (Λ := k) X) (dualNumbersEquiv.{u, u, u} (Λ := k) (k := k))
    (φ.trans (autFunctorDualNumberSectionsEquiv B hZ hk X hdim))

end CurveFamily

end AlgebraicGeometry
