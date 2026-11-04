module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Diagonal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Stability
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductInclusion
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SiteQuasiCompact
public import StacksFrontier.CategoryTheory.PullbackCancelMono

/-!
# Covering an affine formal algebraic space by thickenings (Stacks 0AI9)

Let `X` be the colimit, among the fppf sheaves over a scheme `S` in a big fppf site `B`, of a
nonempty directed diagram `D` of affine schemes over `S` whose transition morphisms are
thickenings. **Stacks 0AI9** says that each stage `X_i` of the presentation maps to `X` by a
morphism that is representable by schemes and that is a thickening: every base change of
`X_i ⟶ X` along a morphism from a represented sheaf is a thickening of schemes.

The argument is the one of the source. Representability of `X_i ⟶ X` is formal from Stacks
0AI8: the diagonal of `X` is representable, and a morphism from a representable sheaf to a
sheaf with representable diagonal is representable. For the thickening assertion, a base
change of `X_i ⟶ X` along a morphism `g : U ⟶ X` out of a represented sheaf is computed
locally on `U`, so it suffices to treat an *affine* `U`. There `U` is a quasi-compact object of
the site, and the transition morphisms of the presentation are monomorphisms of represented
sheaves (a thickening is a closed immersion, hence a monomorphism, and sheafified Yoneda
preserves monomorphisms of the site), so sections of the filtered colimit over `U` are
sections of a single stage: `g` factors through some stage `X_k`. Passing to a common upper
bound `j` of `i` and `k`, the base change of `X_i ⟶ X` along `g` is the base change inside the
site of the transition morphism `X_i ⟶ X_j`, because the stage inclusion `X_j ⟶ X` is a
monomorphism; that base change is a thickening since thickenings of schemes are stable under
base change (Stacks 09ZU). Finally thickenings are Zariski-local at the target, so the
affine-local conclusions glue over the affine cover of `U`.

## Main results

* `AlgebraicGeometry.FormalSpace.relativelyRepresentable_colimitι`: the stage map `X_i ⟶ X` is
  representable by objects of the site — **Stacks 0AI9**.
* `AlgebraicGeometry.FormalSpace.isThickening_colimitι`: every represented base change of the
  stage map `X_i ⟶ X` is a thickening of schemes — **Stacks 0AI9**.

Together these two statements are the content of the tag: `X_i ⟶ X` is representable and a
thickening.

## Implementation notes

The presentation enters as an explicit diagram together with an isomorphism of its colimit with
`X`, rather than through `AlgebraicGeometry.FormalSpace.IsAffineFormalAlgebraicSpace`: the
set-theoretic condition of Stacks 0AIS is not used here, and Stacks 0AIS is deduced from
results of this kind, so stating the hypothesis as affineness of the formal algebraic space
would be circular.

The thickening assertion is phrased as the relative morphism property of
`Stacks.Thickenings.IsThickening` pulled back along `AlgebraicGeometry.BigFppfOver.toScheme`;
that property already contains representability, which the first result records separately
because it is what consumers of the tag use on its own.

The monomorphism helpers now come from the site module
`StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits`; the other helpers here still
duplicate private ones in `Diagonal`; `compact_map_factors_through_filtered_colimit` is not yet in the library.

Subcanonicity of the topology is *not* reproved: `AlgebraicGeometry.bigFppfOver_subcanonical`
is available and is used directly.

Zariski-locality of thickenings at the target is proved here from the identification of a
thickening with a surjective closed immersion; it is the only locality of thickenings this
argument consumes.

## References

* [Stacks Project, Tag 0AI9](https://stacks.math.columbia.edu/tag/0AI9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u v w w₁ w₂

/-- A thickening is exactly a surjective closed immersion, as an equality of morphism
properties of schemes. -/
private theorem isThickening_eq_isClosedImmersion_inf_surjective :
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) =
      (@IsClosedImmersion ⊓ @Surjective : MorphismProperty Scheme.{u}) := by
  ext X Y f
  exact ⟨fun h => ⟨h.1, ⟨h.2⟩⟩, fun h => ⟨h.1, h.2.surj⟩⟩

/-- Thickenings of schemes respect isomorphisms of arrows, being the conjunction of two
properties that do. -/
instance isThickening_respectsIso :
    MorphismProperty.RespectsIso
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) := by
  rw [isThickening_eq_isClosedImmersion_inf_surjective]
  exact MorphismProperty.RespectsIso.inf _ _

/-- Thickenings of schemes are Zariski-local at the target: a thickening is exactly a
surjective closed immersion, and both of those properties are Zariski-local at the target. -/
private instance isThickening_isLocalAtTarget_zariski :
    MorphismProperty.IsLocalAtTarget
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      Scheme.zariskiPrecoverage := by
  rw [isThickening_eq_isClosedImmersion_inf_surjective]
  exact MorphismProperty.IsLocalAtTarget.inf _ _

/-- A morphism to a filtered colimit of sheaves with monomorphic transition morphisms, out of
the sheaf represented by a quasi-compact object of the site, factors through one stage of the
colimit. -/
public theorem compact_map_factors_through_filtered_colimit
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {I : Type w₁} [Category.{w₂} I] [IsFiltered I]
    [HasColimitsOfShape I (Type (max u v))]
    (F : I ⥤ Sheaf J (Type (max u v)))
    (hmono : ∀ i j (f : i ⟶ j), Mono (F.map f)) (U : C)
    (hUqc : J.IsQuasiCompactObject U)
    (f : (Sheaf.sheafifiedYoneda J).obj U ⟶ colimit F) :
    ∃ i : I, ∃ g : (Sheaf.sheafifiedYoneda J).obj U ⟶ F.obj i,
      g ≫ colimit.ι F i = f := by
  let G := (sheafSections J (Type (max u v))).obj (op U)
  have hbij : Function.Bijective (colimit.post F G) :=
    (Sheaf.injective_and_bijective_colimit_post_sheafSections J F U).2.2.1 hUqc hmono
  obtain ⟨z, hz⟩ := hbij.2 ((Sheaf.sectionEquiv J) f)
  let Fsec := F ⋙ G
  obtain ⟨i, x, hx⟩ := Concrete.isColimit_exists_rep Fsec (colimit.isColimit Fsec) z
  let g : (Sheaf.sheafifiedYoneda J).obj U ⟶ F.obj i := (Sheaf.sectionEquiv J).symm x
  refine ⟨i, g, (Sheaf.sectionEquiv J).injective ?_⟩
  calc
    (Sheaf.sectionEquiv J) (g ≫ colimit.ι F i) = (colimit.ι F i).hom.app (op U) x := by
      rw [Sheaf.sectionEquiv_comp]
      exact congrArg ((colimit.ι F i).hom.app (op U)) ((Sheaf.sectionEquiv J).apply_symm_apply x)
    _ = colimit.post F G (colimit.ι Fsec i x) :=
      (ConcreteCategory.congr_hom (colimit.ι_post F G i) x).symm
    _ = colimit.post F G z := congrArg (colimit.post F G) hx
    _ = (Sheaf.sectionEquiv J) f := hz

/-- Sheafified Yoneda on the big fppf site over `S` preserves pullbacks. -/
private instance sheafifiedYoneda_preservesPullbacks (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    PreservesLimitsOfShape WalkingCospan
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) := by
  dsimp [Sheaf.sheafifiedYoneda]
  infer_instance

/-- Sheafified Yoneda on the big fppf site over `S` preserves binary products. -/
private instance sheafifiedYoneda_preservesBinaryProducts (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    PreservesLimitsOfShape (Discrete WalkingPair)
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) := by
  dsimp [Sheaf.sheafifiedYoneda]
  infer_instance

private instance (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS

private instance (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).Full :=
  Sheaf.sheafifiedYoneda_full (BigFppfOver.topology B S hS)

private instance (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).Faithful :=
  Sheaf.sheafifiedYoneda_faithful (BigFppfOver.topology B S hS)

variable (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S)
  {I : Type (u + 1)} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : I ⥤ BigAffineFppf B S hS)
  (hD : ∀ ⦃i j : I⦄ (f : i ⟶ j),
    Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map (D.map f)))
  (X : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  (e : colimit
    (D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) ≅ X)

include hD

/-- A base change of a stage map `X_i ⟶ X` along a morphism out of a sheaf represented by an
*affine* object of the site is a thickening: the testing morphism factors through some stage,
and over a common upper bound the square becomes a base change of a transition morphism of the
presentation. -/
public theorem affine_pullback_thickening
    (i : I) (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ X)
    {V : BigFppfOver B S hS}
    (fst : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj
        ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    (snd : V ⟶ U)
    (hpb : IsPullback fst
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map snd)
      (colimit.ι
        (D ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e.hom) g) :
    Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B S hS).map snd) := by
  let J := BigFppfOver.topology B S hS
  let C := BigFppfOver B S hS
  let q := BigFppfOver.toScheme B S hS
  let F := Sheaf.sheafifiedYoneda J
  let K := D ⋙ BigAffineFppf.inclusion B S hS ⋙ F
  let : HasPullbacks C := inferInstance
  let : PreservesLimitsOfShape WalkingCospan q := inferInstance
  have htrans : ∀ k l (f : k ⟶ l), Mono (K.map f) := by
    intro k l f
    show Mono (F.map ((BigAffineFppf.inclusion B S hS).map (D.map f)))
    have : q.Faithful := inferInstance
    have hm : Mono (q.map ((BigAffineFppf.inclusion B S hS).map (D.map f))) := by
      have hclosed : IsClosedImmersion
          (q.map ((BigAffineFppf.inclusion B S hS).map (D.map f))) := by
        show IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map (D.map f))
        exact (hD f).1
      let : IsClosedImmersion
          (q.map ((BigAffineFppf.inclusion B S hS).map (D.map f))) := hclosed
      infer_instance
    exact Sheaf.mono_sheafifiedYoneda_map_of_mono_underlying J q
      ((BigAffineFppf.inclusion B S hS).map (D.map f)) hm
  let : CompactSpace (q.obj U) := by infer_instance
  have hUqc := AlgebraicGeometry.FormalSpace.isQuasiCompactObject_over_of_compact_scheme B S hS U
  let g₀ := g ≫ e.inv
  obtain ⟨k, gk, hgk⟩ :=
    compact_map_factors_through_filtered_colimit K htrans U hUqc g₀
  let gk' : U ⟶ (BigAffineFppf.inclusion B S hS).obj (D.obj k) := F.preimage gk
  have hgk' : F.map gk' = gk := F.map_preimage _
  obtain ⟨j, hij, hkj⟩ := exists_ge_ge i k
  let α : (BigAffineFppf.inclusion B S hS).obj (D.obj i) ⟶
      (BigAffineFppf.inclusion B S hS).obj (D.obj j) :=
    (BigAffineFppf.inclusion B S hS).map (D.map (homOfLE hij))
  let β : (BigAffineFppf.inclusion B S hS).obj (D.obj k) ⟶
      (BigAffineFppf.inclusion B S hS).obj (D.obj j) :=
    (BigAffineFppf.inclusion B S hS).map (D.map (homOfLE hkj))
  let g' : U ⟶ (BigAffineFppf.inclusion B S hS).obj (D.obj j) := gk' ≫ β
  have hg' : F.map g' ≫ colimit.ι K j ≫ e.hom = g := by
    calc
      F.map g' ≫ colimit.ι K j ≫ e.hom =
          (gk ≫ K.map (homOfLE hkj)) ≫ colimit.ι K j ≫ e.hom := by
            dsimp [g']
            simp only [Functor.map_comp]
            rw [hgk']
            rfl
      _ = gk ≫ colimit.ι K k ≫ e.hom := by rw [Category.assoc, colimit.w_assoc]
      _ = g₀ ≫ e.hom := by
        simpa only [Category.assoc] using congrArg (fun t => t ≫ e.hom) hgk
      _ = g := by
        show (g ≫ e.inv) ≫ e.hom = g
        rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  let p₁ := pullback.fst α g'
  let p₂ := pullback.snd α g'
  have hpbC : IsPullback p₁ p₂ α g' := IsPullback.of_hasPullback α g'
  have hpbScheme : IsPullback (q.map p₁) (q.map p₂) (q.map α) (q.map g') := hpbC.map q
  have hα : Stacks.Thickenings.IsThickening (q.map α) := by
    show Stacks.Thickenings.IsThickening
      ((BigAffineFppf.toScheme B S hS).map (D.map (homOfLE hij)))
    exact hD (homOfLE hij)
  have hp₂ : Stacks.Thickenings.IsThickening (q.map p₂) :=
    Stacks.Thickenings.isThickening_isStableUnderBaseChange.of_isPullback hpbScheme hα
  have hmono : Mono (colimit.ι K j ≫ e.hom) := by
    have hm : Mono (colimit.ι K j) := Sheaf.mono_colimit_ι_of_mono_transition K htrans j
    infer_instance
  have hinner : IsPullback (F.map p₁) (F.map p₂) (F.map α) (F.map g') := hpbC.map F
  have houter := isPullback_comp_mono hinner (colimit.ι K j ≫ e.hom)
  have hαeq : F.map α ≫ (colimit.ι K j ≫ e.hom) = colimit.ι K i ≫ e.hom :=
    colimit.w_assoc K (homOfLE hij) e.hom
  have houter' : IsPullback (F.map p₁) (F.map p₂) (colimit.ι K i ≫ e.hom) g :=
    houter.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) hαeq hg'
  let ePB := houter'.isoIsPullback
    (F.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i))) (F.obj U) hpb
  let eC := F.preimageIso ePB
  have heMap : F.map eC.hom = ePB.hom := F.map_preimage _
  have heC : eC.hom ≫ snd = p₂ := by
    apply F.map_injective
    rw [F.map_comp, heMap]
    exact houter'.isoIsPullback_hom_snd
      (F.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj i))) (F.obj U) hpb
  have hArrow : Arrow.mk (q.map p₂) ≅ Arrow.mk (q.map snd) :=
    Arrow.isoMk (q.mapIso eC) (Iso.refl _) (by
      show q.map eC.hom ≫ q.map snd = q.map p₂
      rw [← q.map_comp, heC])
  exact (MorphismProperty.arrow_mk_iso_iff
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) hArrow).mp hp₂

/-- **Stacks 0AI9.** A stage of a directed presentation of an affine formal algebraic space by
affine schemes with thickening transition morphisms maps representably to the colimit: every
base change of `X_i ⟶ X` along a morphism from a represented sheaf is again represented by an
object of the site. -/
@[stacks 0AI9 "representability"]
theorem relativelyRepresentable_colimitι (i : I) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable
      (colimit.ι
        (D ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e.hom) := by
  let J := BigFppfOver.topology B S hS
  let C := BigFppfOver B S hS
  let F := Sheaf.sheafifiedYoneda J
  let : HasPullbacks C := inferInstance
  let : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C
  exact Functor.relativelyRepresentable.of_diag (diagonal_isClosedImmersion B S hS D hD X e).1
    (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda J) i ≫ e.hom)

/-- **Stacks 0AI9.** A stage of a directed presentation of an affine formal algebraic space by
affine schemes with thickening transition morphisms maps to the colimit by a thickening: the
map `X_i ⟶ X` is representable, and each of its base changes along a represented sheaf is a
thickening of schemes. -/
@[stacks 0AI9 "thickening"]
theorem isThickening_colimitι (i : I) :
    (MorphismProperty.relative
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
      (MorphismProperty.inverseImage
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)))
      (colimit.ι
        (D ⋙ BigAffineFppf.inclusion B S hS ⋙
          Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i ≫ e.hom) := by
  let J := BigFppfOver.topology B S hS
  let C := BigFppfOver B S hS
  let q := BigFppfOver.toScheme B S hS
  let F := Sheaf.sheafifiedYoneda J
  let fi := colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ F) i ≫ e.hom
  let : HasPullbacks C := inferInstance
  let : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C
  let hrel := relativelyRepresentable_colimitι B S hS D hD X e i
  let P := MorphismProperty.inverseImage
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) q
  let : P.RespectsIso := MorphismProperty.RespectsIso.inverseImage
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) q
  apply MorphismProperty.relative.of_exists
  intro U g
  obtain ⟨V, s, fst, hpbGlobal⟩ := hrel g
  have hs : P s := by
    show Stacks.Thickenings.IsThickening (q.map s)
    let A := (q.obj U).affineCover
    have hlocal (a : A.I₀) :
        Stacks.Thickenings.IsThickening (pullback.snd (q.map s) (A.f a)) := by
      let W₀ : B.Schemes := ⟨A.X a,
        Scheme.size_lt_of_isOpenImmersion (A.f a) U.left.property⟩
      let u₀ : W₀ ⟶ U.left := B.inclusion.preimage (show
        B.inclusion.obj W₀ ⟶ B.inclusion.obj U.left from A.f a)
      let W : C := Over.mk (u₀ ≫ U.hom)
      let aW : W ⟶ U := Over.homMk u₀ rfl
      let gW := F.map aW ≫ g
      let : IsAffine (q.obj W) := by
        show IsAffine (A.X a)
        infer_instance
      let q₁ := pullback.fst s aW
      let q₂ := pullback.snd s aW
      have hQ : IsPullback q₁ q₂ s aW := IsPullback.of_hasPullback s aW
      have hQsheaf : IsPullback (F.map q₁) (F.map q₂) (F.map s) (F.map aW) := hQ.map F
      have hpbW : IsPullback (F.map q₁ ≫ fst) (F.map q₂) fi gW := by
        simpa only [gW] using hQsheaf.paste_horiz hpbGlobal
      have hthickW := affine_pullback_thickening B S hS D hD X e i W gW
        (F.map q₁ ≫ fst) q₂ hpbW
      have hQscheme : IsPullback (q.map q₁) (q.map q₂) (q.map s) (q.map aW) := hQ.map q
      have hqaw : q.map aW = A.f a := by
        show B.inclusion.map u₀ = A.f a
        exact B.inclusion.map_preimage _
      have hcanon : IsPullback (pullback.fst (q.map s) (A.f a))
          (pullback.snd (q.map s) (A.f a)) (q.map s) (A.f a) :=
        IsPullback.of_hasPullback (q.map s) (A.f a)
      have hQscheme' : IsPullback (q.map q₁) (q.map q₂) (q.map s) (A.f a) := by
        simpa only [hqaw] using hQscheme
      let eQ := hQscheme'.isoIsPullback (q.obj V) (q.obj W) hcanon
      have hArrow : Arrow.mk (q.map q₂) ≅
          Arrow.mk (pullback.snd (q.map s) (A.f a)) :=
        Arrow.isoMk eQ (Iso.refl _) (hQscheme'.isoIsPullback_hom_snd
          (q.obj V) (q.obj W) hcanon)
      exact (MorphismProperty.arrow_mk_iso_iff
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) hArrow).mp hthickW
    exact (inferInstance :
      MorphismProperty.IsLocalAtTarget
        (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
        Scheme.zariskiPrecoverage).of_zeroHypercover A hlocal
  exact ⟨V, fst, s, hpbGlobal, by simpa [P] using hs⟩

end AlgebraicGeometry.FormalSpace

end
