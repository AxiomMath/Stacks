module

public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroExtension

/-!
# Pushing a square-zero extension forward along a morphism

A square-zero extension of the structure sheaf of `Z` can be pushed forward along a morphism
`g : Z ⟶ V` whenever the canonical comparison `𝒪_V ⟶ g_*𝒪_Z` is an isomorphism: the extension
sheaf `A` becomes `g_*A`, the quotient map becomes `g_*A ⟶ g_*𝒪_Z ≅ 𝒪_V`, and the kernel
becomes `g_*I`.

## Main definitions

* `Stacks.Thickenings.SquareZeroExtension.pushforward`: the pushed-forward extension.
* `Stacks.Thickenings.SquareZeroExtension.toBaseC`: the structure map `𝒪_S ⟶ f_*A` of an
  extension, with its target read along the structure morphism of the scheme.
* `Stacks.Thickenings.structureComparisonInv`: the inverse of the structure-sheaf comparison.

## Main results

* `Stacks.Thickenings.SquareZeroExtension.toBase_base`: the structure morphism of the extension
  has the same underlying continuous map as the structure morphism of the scheme.
* `Stacks.Thickenings.SquareZeroExtension.toBaseC_comp`: the structure map of the extension is
  compatible with the quotient map, which is the sheaf component of the field `over_base`.
* `Stacks.Thickenings.isLocallySurjective_comp_structureComparisonInv`: local surjectivity of
  `g_*π` gives the local surjectivity the pushforward asks for.
* `Stacks.Thickenings.SquareZeroExtension.pushforward_A`, `pushforward_π_hom`, `pushforward_I`
  and `pushforward_ι`: the pushed-forward extension is built out of `g_*A`, `g_*π` and `g_*I`.

## Implementation notes

Two hypotheses are genuine input rather than bookkeeping.  Local surjectivity of the pushed-forward
quotient map is not automatic — it is what the vanishing of `R¹g_*I` buys — and quasi-coherence of
`g_*I` is not automatic either, direct image preserving quasi-coherence only under finiteness
assumptions on `g`.  Both are therefore taken as hypotheses; everything else is carried across
by the construction.

The fields `inclusion_base` and `inclusion_sheaf` of
`Stacks.Thickenings.SquareZeroExtension` pin the canonical inclusion only up to an equality of
continuous maps and a heterogeneous equality of sheaf components, and `over_base` is an equality of
morphisms of sheafed spaces whose sheaf components therefore live in types that agree only
propositionally.  Reading those back needs the comparison isomorphism
`TopCat.Presheaf.pushforwardEq`, which is the identity whenever the two continuous maps are the
same (`Stacks.Thickenings.pushforwardEq_hom_self`); `toBaseC_comp` discharges all three at once by
taking the extension apart and substituting its underlying continuous maps, after which the sheaf
component of a composite of sheafed-space morphisms is the expected composite on the nose.

`Stacks.Thickenings.structureComparisonInv` names `inv g.c` rather than leaving it inline because
the target of the quotient map of the pushed-forward extension is spelled as a direct image along
the identity, and as the underlying presheaf of the structure sheaf of `V`; neither unfolds to
`V.presheaf` at reducible transparency, so instance synthesis for `IsIso` does not fire there.

## References

* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe u w

namespace Stacks.Thickenings

/-! ### The comparison isomorphism of equal continuous maps -/

/-- **The comparison isomorphism of a continuous map with itself is the identity.** Its
components are `ℱ.map` of a morphism of opens, and those form a subsingleton. -/
theorem pushforwardEq_hom_self {X Y : TopCat.{w}} {f : X ⟶ Y} (h : f = f)
    (ℱ : TopCat.Presheaf CommRingCat.{u} X) :
    (TopCat.Presheaf.pushforwardEq h ℱ).hom = 𝟙 _ := by
  refine NatTrans.ext (funext fun U => ?_)
  rw [TopCat.Presheaf.pushforwardEq_hom_app]
  exact (congrArg ℱ.map (Subsingleton.elim _ (𝟙 _))).trans (ℱ.map_id _)

/-! ### The structure morphism of an extension -/

variable {Z V S : Scheme.{u}}

/-- **The structure morphism of a square-zero extension lies over the structure morphism of the
scheme.** The two have the same underlying continuous map, because the canonical inclusion of
`X` into the extension is the identity on points. -/
theorem SquareZeroExtension.toBase_base {X : Scheme.{u}} {f : X ⟶ S}
    (E : SquareZeroExtension f) : E.toBase.hom.base = f.base := by
  have h : E.inclusion.hom.base ≫ E.toBase.hom.base = f.base :=
    congrArg (fun α : X.toSheafedSpace ⟶ S.toSheafedSpace => α.hom.base) E.over_base
  have h2 : E.inclusion.hom.base ≫ E.toBase.hom.base
      = 𝟙 (X : TopCat) ≫ E.toBase.hom.base :=
    congrArg (fun t => t ≫ E.toBase.hom.base) E.inclusion_base
  exact (Category.id_comp _).symm.trans (h2.symm.trans h)

/-- **The structure map of a square-zero extension, read along the structure morphism of the
scheme.** The field `toBase` provides a map `𝒪_S ⟶ (E.toBase.base)_*A`, whose underlying
continuous map is only propositionally the one of `f`; this is the same map with its target
rewritten as `f_*A`. -/
def SquareZeroExtension.toBaseC {X : Scheme.{u}} {f : X ⟶ S} (E : SquareZeroExtension f) :
    S.presheaf ⟶ (TopCat.Presheaf.pushforward CommRingCat.{u} f.base).obj E.A.presheaf :=
  E.toBase.hom.c ≫ (TopCat.Presheaf.pushforwardEq E.toBase_base E.A.presheaf).hom

/-- **The quotient map of a square-zero extension is compatible with the structure morphism.**
Composing the structure map `𝒪_S ⟶ f_*A` of the extension with the direct image of the quotient
`A ⟶ 𝒪_X` gives the structure map `𝒪_S ⟶ f_*𝒪_X` of the scheme.  This is the sheaf component of
the field `over_base`, with the two heterogeneous identifications of
`Stacks.Thickenings.SquareZeroExtension` discharged. -/
theorem SquareZeroExtension.toBaseC_comp {X : Scheme.{u}} {f : X ⟶ S}
    (E : SquareZeroExtension f) :
    E.toBaseC ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} f.base).map E.π.hom = f.c := by
  obtain ⟨A, π, hls, ⟨⟨ibase, ic⟩⟩, hb, hs, ⟨⟨tbase, tc⟩⟩, ob, I, hq, ι, nat, mk, ek, sz⟩ := E
  replace hb : ibase = 𝟙 (X : TopCat) := hb
  subst hb
  replace hs : ic = π.hom := eq_of_heq hs
  subst hs
  have htb : tbase = f.base :=
    congrArg (fun α : X.toSheafedSpace ⟶ S.toSheafedSpace => α.hom.base) ob
  subst htb
  have hc : HEq (tc ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} f.base).map π.hom)
      ((LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom f)).hom.c) := by
    rw [← ob]
    exact HEq.rfl
  change (tc ≫ (TopCat.Presheaf.pushforwardEq _ A.presheaf).hom) ≫ _ = _
  erw [pushforwardEq_hom_self, Category.comp_id]
  exact eq_of_heq hc

/-! ### Inverting the structure-sheaf comparison -/

/-- **The inverse structure-sheaf comparison** `g_*𝒪_Z ⟶ 𝒪_V` of a morphism of schemes whose
comparison `𝒪_V ⟶ g_*𝒪_Z` is an isomorphism. -/
def structureComparisonInv (g : Z ⟶ V) [IsIso g.c] :
    (TopCat.Presheaf.pushforward CommRingCat.{u} g.base).obj Z.presheaf ⟶ V.presheaf :=
  inv g.c

/-- The structure-sheaf comparison followed by its inverse is the identity. -/
@[simp]
theorem c_comp_structureComparisonInv (g : Z ⟶ V) [IsIso g.c] :
    g.c ≫ structureComparisonInv g = 𝟙 _ :=
  IsIso.hom_inv_id g.c

/-- The inverse structure-sheaf comparison followed by the comparison is the identity. -/
@[simp]
theorem structureComparisonInv_comp_c (g : Z ⟶ V) [IsIso g.c] :
    structureComparisonInv g ≫ g.c = 𝟙 _ :=
  IsIso.inv_hom_id g.c

/-- **The inverse comparison inverts on sections.** Applying the inverse comparison to the
comparison of a section recovers the section. -/
theorem structureComparisonInv_app_c_app_apply (g : Z ⟶ V) [IsIso g.c] (U : (Opens V)ᵒᵖ)
    (v : V.presheaf.obj U) :
    ((structureComparisonInv g).app U).hom ((g.c.app U).hom v) = v := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, c_comp_structureComparisonInv,
    NatTrans.id_app, ConcreteCategory.id_apply]

/-- **The inverse comparison is locally surjective**, being split epi: the comparison itself is a
section of it. -/
theorem isLocallySurjective_structureComparisonInv (g : Z ⟶ V) [IsIso g.c] :
    TopCat.Presheaf.IsLocallySurjective (structureComparisonInv g) :=
  CategoryTheory.Presheaf.isLocallySurjective_of_surjective _ _
    fun U v => ⟨(g.c.app U).hom v, structureComparisonInv_app_c_app_apply g U v⟩

/-- **The structure-sheaf comparison inverts on sections.** Applying the comparison to the
inverse comparison of a section recovers the section. -/
theorem c_app_structureComparisonInv_app_apply (g : Z ⟶ V) [IsIso g.c] (U : (Opens V)ᵒᵖ)
    (y : ((TopCat.Presheaf.pushforward CommRingCat.{u} g.base).obj Z.presheaf).obj U) :
    (g.c.app U).hom (((structureComparisonInv g).app U).hom y) = y := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, structureComparisonInv_comp_c,
    NatTrans.id_app, ConcreteCategory.id_apply]

/-- **Local surjectivity survives the inverse comparison.** If the direct image `g_*A ⟶ g_*𝒪_Z`
of a surjection onto the structure sheaf is locally surjective, then so is its composite with
the inverse comparison, which is the quotient map of the pushed-forward extension. -/
theorem isLocallySurjective_comp_structureComparisonInv (g : Z ⟶ V) [IsIso g.c]
    {A : TopCat.Presheaf CommRingCat.{u} Z} (p : A ⟶ Z.presheaf)
    (hp : TopCat.Presheaf.IsLocallySurjective
      ((TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map p)) :
    TopCat.Presheaf.IsLocallySurjective
      ((TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map p
        ≫ structureComparisonInv g) := by
  have : CategoryTheory.Presheaf.IsLocallySurjective _
    ((TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map p) := hp
  have : CategoryTheory.Presheaf.IsLocallySurjective _ (structureComparisonInv g) :=
    isLocallySurjective_structureComparisonInv g
  exact CategoryTheory.Presheaf.isLocallySurjective_comp _ _ _

/-! ### The pushforward -/

/-- **The pushforward of a square-zero extension along a morphism.** Let `g : Z ⟶ V` be a
morphism of schemes whose structure-sheaf comparison `𝒪_V ⟶ g_*𝒪_Z` is an isomorphism, and let
`k : V ⟶ S`.  A square-zero extension of `𝒪_Z` over `S` is pushed forward to one of `𝒪_V` over
`S`: the extension sheaf is `g_*A`, the quotient map is `g_*A ⟶ g_*𝒪_Z ≅ 𝒪_V`, and the kernel is
`g_*I`.

The two hypotheses are the content.  `hπ` says that `g_*A ⟶ g_*𝒪_Z` is still locally surjective,
which is what the vanishing of `R¹g_*I` provides, and `hqc` says that `g_*I` is still
quasi-coherent.  Everything else — the square-zero condition, the module structure of the kernel,
and the algebra structure over `S` — is carried across by the construction. -/
def SquareZeroExtension.pushforward (g : Z ⟶ V) (k : V ⟶ S) (E : SquareZeroExtension (g ≫ k))
    [IsIso g.c]
    (hπ : TopCat.Presheaf.IsLocallySurjective
      ((TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom
        ≫ structureComparisonInv g))
    (hqc : ((Scheme.Modules.pushforward g).obj E.I).IsQuasicoherent) :
    SquareZeroExtension k where
  A := (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj E.A
  π := ⟨(TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom
    ≫ structureComparisonInv g⟩
  locallySurjective_π := hπ
  inclusion := InducedCategory.homMk
    { base := 𝟙 (V : TopCat)
      c := (TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom
        ≫ structureComparisonInv g }
  inclusion_base := rfl
  inclusion_sheaf := HEq.rfl
  toBase := InducedCategory.homMk { base := k.base, c := E.toBaseC }
  over_base := by
    refine SheafedSpace.ext _ _ rfl ?_
    have h1 : E.toBaseC ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} k.base).map
        ((TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom) = (g ≫ k).c :=
      E.toBaseC_comp
    have h2 : (g ≫ k).c
        = k.c ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} k.base).map g.c := rfl
    have hmc : (TopCat.Presheaf.pushforward CommRingCat.{u} k.base).map
          ((TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom
            ≫ structureComparisonInv g)
        = (TopCat.Presheaf.pushforward CommRingCat.{u} k.base).map
            ((TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom) ≫
          (TopCat.Presheaf.pushforward CommRingCat.{u} k.base).map
            (structureComparisonInv g) :=
      Functor.map_comp _ _ _
    have step1 : E.toBaseC ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} k.base).map
          ((TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom
            ≫ structureComparisonInv g)
        = (E.toBaseC ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} k.base).map
            ((TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom)) ≫
          (TopCat.Presheaf.pushforward CommRingCat.{u} k.base).map
            (structureComparisonInv g) :=
      (congrArg (fun t => E.toBaseC ≫ t) hmc).trans (Category.assoc _ _ _).symm
    have step2 : (E.toBaseC ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} k.base).map
            ((TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom)) ≫
          (TopCat.Presheaf.pushforward CommRingCat.{u} k.base).map (structureComparisonInv g)
        = (g ≫ k).c ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} k.base).map
            (structureComparisonInv g) :=
      congrArg (fun t => t ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} k.base).map
        (structureComparisonInv g)) h1
    have step3 : (g ≫ k).c ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} k.base).map
          (structureComparisonInv g)
        = k.c ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} k.base).map
            (g.c ≫ structureComparisonInv g) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun t => k.c ≫ t) (Functor.map_comp _ _ _).symm)
    have step4 : k.c ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} k.base).map
          (g.c ≫ structureComparisonInv g) = k.c :=
      (congrArg (fun t => k.c ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} k.base).map t)
          (c_comp_structureComparisonInv g)).trans
        ((congrArg (fun t => k.c ≫ t)
            ((TopCat.Presheaf.pushforward CommRingCat.{u} k.base).map_id _)).trans
          (Category.comp_id _))
    have hfin := step1.trans (step2.trans (step3.trans step4))
    change (E.toBaseC ≫ (TopCat.Presheaf.pushforward CommRingCat.{u} k.base).map
        ((TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom
          ≫ structureComparisonInv g)) ≫
      Functor.whiskerRight (eqToHom rfl) V.presheaf = k.c
    rw [eqToHom_refl, Functor.whiskerRight_id']
    exact (Category.comp_id _).trans hfin
  I := (Scheme.Modules.pushforward g).obj E.I
  quasicoherent := hqc
  ι U := E.ι (op ((Opens.map g.base).obj U.unop))
  naturality gm x := E.naturality ((Opens.map g.base).op.map gm) x
  mem_kernel U x :=
    (congrArg (fun y => ((structureComparisonInv g).app U).hom y) (E.mem_kernel _ x)).trans
      (map_zero _)
  exact_kernel U a ha := by
    have ha0 : ((structureComparisonInv g).app U).hom
        ((E.π.hom.app (op ((Opens.map g.base).obj U.unop))).hom a) = 0 := ha
    have ha' : (E.π.hom.app (op ((Opens.map g.base).obj U.unop))).hom a = 0 := by
      have h := congrArg (fun y => (g.c.app U).hom y) ha0
      rw [map_zero] at h
      exact (c_app_structureComparisonInv_app_apply g U _).symm.trans h
    exact E.exact_kernel (op ((Opens.map g.base).obj U.unop)) a ha'
  smul_lift U a x := by
    have hr : (E.I.val.obj (op ((Opens.map g.base).obj U.unop))).smul
          ((g.c.app U).hom (((structureComparisonInv g).app U).hom
            ((E.π.hom.app (op ((Opens.map g.base).obj U.unop))).hom a)))
        = (E.I.val.obj (op ((Opens.map g.base).obj U.unop))).smul
            ((E.π.hom.app (op ((Opens.map g.base).obj U.unop))).hom a) :=
      congrArg _ (c_app_structureComparisonInv_app_apply g U _)
    refine Eq.trans ?_ (E.smul_lift (op ((Opens.map g.base).obj U.unop)) a x)
    exact congrArg (fun m => E.ι (op ((Opens.map g.base).obj U.unop)) m)
      (congrArg (fun φ => (AddCommGrpCat.Hom.hom φ.asHom) x) hr)
  square_zero U x y := E.square_zero (op ((Opens.map g.base).obj U.unop)) x y

/-! ### Reading the pushforward off its construction -/

section Projections

variable (g : Z ⟶ V) (k : V ⟶ S) (E : SquareZeroExtension (g ≫ k)) [IsIso g.c]
  (hπ : TopCat.Presheaf.IsLocallySurjective
    ((TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom
      ≫ structureComparisonInv g))
  (hqc : ((Scheme.Modules.pushforward g).obj E.I).IsQuasicoherent)

/-- The extension sheaf of the pushforward is the direct image of the extension sheaf. -/
@[simp]
theorem SquareZeroExtension.pushforward_A :
    (SquareZeroExtension.pushforward g k E hπ hqc).A =
      (TopCat.Sheaf.pushforward CommRingCat.{u} g.base).obj E.A :=
  rfl

/-- The quotient map of the pushforward is the direct image of the quotient map, followed by the
inverse structure-sheaf comparison. -/
@[simp]
theorem SquareZeroExtension.pushforward_π_hom :
    (SquareZeroExtension.pushforward g k E hπ hqc).π.hom =
      (TopCat.Presheaf.pushforward CommRingCat.{u} g.base).map E.π.hom
        ≫ structureComparisonInv g :=
  rfl

/-- The kernel of the pushforward is the direct image of the kernel. -/
@[simp]
theorem SquareZeroExtension.pushforward_I :
    (SquareZeroExtension.pushforward g k E hπ hqc).I =
      (Scheme.Modules.pushforward g).obj E.I :=
  rfl

/-- The kernel inclusion of the pushforward is the one of the extension, read over the
preimage. -/
@[simp]
theorem SquareZeroExtension.pushforward_ι (U : (Opens V)ᵒᵖ) :
    (SquareZeroExtension.pushforward g k E hπ hqc).ι U =
      E.ι (op ((Opens.map g.base).obj U.unop)) :=
  rfl

end Projections

end Stacks.Thickenings

end
