module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.Diagram
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.StackIsom
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.MorSheafFromIsom

/-!
# The `Isom` presheaves of the category `ℋ_d` of finite locally free covers are sheaves

Let `S` be a scheme contained in a big fppf site `B` and let `d` be a natural number. This file
proves the second of the three conditions of Stacks 05WB for the category `ℋ_d` of degree-`d`
finite locally free covers of `AlgebraicGeometry.Stack.finiteCoverCategory`: for two covers
`Z ⟶ U` and `Z' ⟶ U` over one and the same object `U` of the big fppf site, the presheaf
`Isom((U, Z), (U, Z'))` on the site over `U` is a sheaf.

## Main results

* `AlgebraicGeometry.Stack.FiniteCover.Hom.f_eq_of_fibreHom`: the base component of a morphism
  of `ℋ_d` lying in a fibre.
* `AlgebraicGeometry.Stack.FiniteCover.Hom.isPullback_g`: a commuting square of morphisms of
  `ℋ_d` whose base components form a cartesian square has cartesian cover components.
* `AlgebraicGeometry.Stack.isom_isSheaf_finiteCoverProjection`: the `Isom` presheaves of `ℋ_d`
  are sheaves.
* `AlgebraicGeometry.Stack.isMorSheaf_finiteCoverProjection`: the presheaves `Mor(x, y)` of
  `ℋ_d` on the localized sites are sheaves.

## References

* [Stacks Project, Tag 05WB](https://stacks.math.columbia.edu/tag/05WB)
* [Stacks Project, Tag 05WC](https://stacks.math.columbia.edu/tag/05WC)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}

namespace FiniteCover

/-- The base component of a morphism of `ℋ_d` which lies in the fibre over `U` is the
identification of its two base objects with `U`. -/
theorem Hom.f_eq_of_fibreHom {P Q : FiniteCover B S hS d} {U : BigFppfOver B S hS}
    (hP : P.U = U) (hQ : Q.U = U) (φ : P ⟶ Q)
    (hφ : Functor.FibreHom (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d))
      P Q hP hQ φ) :
    φ.f = eqToHom hP ≫ eqToHom hQ.symm := by
  have := hφ
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d))
    (eqToHom hP ≫ eqToHom hQ.symm) φ).symm

/-- **A commuting square of morphisms of `ℋ_d` whose base components form a cartesian square has
cartesian cover components.** -/
theorem Hom.isPullback_g {P Q R T : FiniteCover B S hS d}
    (a : P ⟶ Q) (b : P ⟶ R) (c : Q ⟶ T) (e : R ⟶ T) (h : a ≫ c = b ≫ e)
    (sq : IsPullback a.f b.f c.f e.f) : IsPullback a.g b.g c.g e.g := by
  have houter := (a.square.paste_vert sq).flip
  rw [← b.square.w, ← c.square.w] at houter
  have hcomm : b.g ≫ e.g = a.g ≫ c.g := (congrArg Hom.g h).symm
  exact (houter.of_right hcomm e.square.flip).flip

end FiniteCover

/-- **Condition (2) of Stacks 05WB for the category `ℋ_d` of degree-`d` finite locally free
covers: its `Isom` presheaves are sheaves.** For two covers `P` and `Q` lying over one and the
same object `U` of the big fppf site and a covering family `{V i ⟶ U}` whose overlaps are genuine
fibre products `V i ×_U V j`, a family of isomorphisms `P|_{V i} ⟶ Q|_{V i}` which agree on the
overlaps glues to a unique isomorphism `P ⟶ Q` of the fibre over `U` restricting to the given
ones. -/
theorem isom_isSheaf_finiteCoverProjection {U : BigFppfOver B S hS}
    (P Q : FiniteCover B S hS d)
    (hP : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).obj P = U)
    (hQ : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).obj Q = U)
    {I : Type w} (V : I → BigFppfOver B S hS) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology B S hS U)
    (Vij : I → I → BigFppfOver B S hS)
    (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (xr : ∀ i, Functor.Restriction (finiteCoverProjection (B := B) (S := S) (hS := hS)
      (d := d)) (f i) P hP)
    (yr : ∀ i, Functor.Restriction (finiteCoverProjection (B := B) (S := S) (hS := hS)
      (d := d)) (f i) Q hQ)
    (xrij : ∀ i j, Functor.Restriction (finiteCoverProjection (B := B) (S := S) (hS := hS)
      (d := d)) (pr₁ i j ≫ f i) P hP)
    (yrij : ∀ i j, Functor.Restriction (finiteCoverProjection (B := B) (S := S) (hS := hS)
      (d := d)) (pr₁ i j ≫ f i) Q hQ) :
    Functor.IsomIsSheafFor (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d))
      P Q hP hQ V f Vij pr₁ pr₂ hVij xr yr xrij yrij := by
  intro φ hφ hiso hcompat
  have hP' : P.U = U := hP
  have hQ' : Q.U = U := hQ
  have hxpt (i : I) : (xr i).pt.U = V i := (xr i).hpt
  have hypt (i : I) : (yr i).pt.U = V i := (yr i).hpt
  have hxptij (i j : I) : (xrij i j).pt.U = Vij i j := (xrij i j).hpt
  let t i := (xr i).pt
  let ν i := (xr i).hom
  let μ i := φ i ≫ (yr i).hom
  let c i j := Functor.Restriction.compTo (finiteCoverProjection (B := B) (S := S) (hS := hS)
    (d := d)) (pr₁ i j) (f i) rfl (xr i) (xrij i j)
  let e i j := Functor.Restriction.compTo (finiteCoverProjection (B := B) (S := S) (hS := hS)
    (d := d)) (pr₂ i j) (f j) (hVij i j).w (xr j) (xrij i j)
  have hν (i j : I) : c i j ≫ ν i = e i j ≫ ν j := by
    dsimp only [c, e, ν]
    rw [Functor.Restriction.compTo_hom, Functor.Restriction.compTo_hom]
  have hμ (i j : I) : c i j ≫ μ i = e i j ≫ μ j := by
    obtain ⟨γ, -, hγi, hγj⟩ := hcompat i j
    change γ ≫ _ = c i j ≫ φ i at hγi
    change γ ≫ _ = e i j ≫ φ j at hγj
    dsimp only [μ]
    rw [← Category.assoc, ← hγi, Category.assoc, Functor.Restriction.compTo_hom,
      ← Category.assoc, ← hγj, Category.assoc, Functor.Restriction.compTo_hom]
  have hνf (i : I) : (ν i).f = eqToHom (hxpt i) ≫ f i ≫ eqToHom hP'.symm := by
    have := (xr i).isHomLift_hom
    exact CategoryTheory.IsHomLift.fac'
      (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) (f i) (xr i).hom
  have hνcover : Sieve.ofArrows (fun i => (t i).U) (fun i => (ν i).f) ∈
      BigFppfOver.topology B S hS P.U := by
    refine FiniteHilbert.ofArrows_mem_of_isPullback _ f hf (eqToHom hP') (fun i => (ν i).f)
      (fun i => eqToHom (hxpt i)) fun i => ?_
    exact IsPullback.of_vert_isIso ⟨by simp [hνf]⟩
  have hcf (i j : I) : (c i j).f =
      eqToHom (hxptij i j) ≫ pr₁ i j ≫ eqToHom (hxpt i).symm :=
    Functor.Restriction.compTo_map _ (pr₁ i j) (f i) rfl (xr i) (xrij i j)
  have hef (i j : I) : (e i j).f =
      eqToHom (hxptij i j) ≫ pr₂ i j ≫ eqToHom (hxpt j).symm :=
    Functor.Restriction.compTo_map _ (pr₂ i j) (f j) (hVij i j).w (xr j) (xrij i j)
  have sq (i j : I) : IsPullback (c i j).f (e i j).f (ν i).f (ν j).f := by
    rw [hcf i j, hef i j, hνf, hνf]
    exact (hVij i j).of_iso (eqToIso (hxptij i j).symm) (eqToIso (hxpt i).symm)
      (eqToIso (hxpt j).symm) (eqToIso hP'.symm) (by simp) (by simp) (by simp) (by simp)
  let fU : P.U ≅ Q.U := eqToIso (hP'.trans hQ'.symm)
  have hfU : fU.hom = eqToHom hP' ≫ eqToHom hQ'.symm := (eqToHom_trans hP' hQ'.symm).symm
  have hμf (i : I) : (ν i).f ≫ fU.hom = (μ i).f := by
    have := (yr i).isHomLift_hom
    have hy : (yr i).hom.f = eqToHom (hypt i) ≫ f i ≫ eqToHom hQ'.symm :=
      CategoryTheory.IsHomLift.fac'
        (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) (f i) (yr i).hom
    have hi := FiniteCover.Hom.f_eq_of_fibreHom (hxpt i) (hypt i) (φ i) (hφ i)
    show (ν i).f ≫ fU.hom = (φ i).f ≫ (yr i).hom.f
    simp [hνf, hi, hy, hfU]
  have hμcover : Sieve.ofArrows (fun i => (t i).U) (fun i => (μ i).f) ∈
      BigFppfOver.topology B S hS Q.U := by
    have hpb := (BigFppfOver.topology B S hS).pullback_stable fU.inv hνcover
    have heq : Sieve.pullback fU.inv
          (Sieve.ofArrows (fun i => (t i).U) (fun i => (ν i).f)) =
        Sieve.ofArrows (fun i => (t i).U) (fun i => (ν i).f ≫ fU.hom) :=
      Sieve.pullback_ofArrows_of_iso _ _ fU.symm
    simpa only [heq, hμf] using hpb
  have sqμ (i j : I) : IsPullback (c i j).f (e i j).f (μ i).f (μ j).f :=
    (sq i j).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) fU
      (by simp) (by simp) (by simpa using hμf i) (by simpa using hμf j)
  have hνsource := FiniteHilbert.ofArrows_mem_of_isPullback _ (fun i => (ν i).f) hνcover P.q
    (fun i => (ν i).g) (fun i => (t i).q) (fun i => (ν i).square)
  have hμsource := FiniteHilbert.ofArrows_mem_of_isPullback _ (fun i => (μ i).f) hμcover Q.q
    (fun i => (μ i).g) (fun i => (t i).q) (fun i => (μ i).square)
  obtain ⟨gZ, hg⟩ := FiniteHilbert.exists_site_iso_of_covers (fun i => (ν i).g)
    (fun i => (μ i).g) hνsource hμsource (fun i j => (c i j).g) (fun i j => (e i j).g)
    (fun i j => FiniteCover.Hom.isPullback_g _ _ _ _ (hν i j) (sq i j))
    (fun i j => FiniteCover.Hom.isPullback_g _ _ _ _ (hμ i j) (sqμ i j))
  have hfg : gZ.hom ≫ Q.q = P.q ≫ fU.hom := by
    refine FiniteHilbert.site_hom_ext (fun i => (ν i).g) hνsource fun i => ?_
    rw [← Category.assoc, hg, (μ i).square.w, ← hμf, ← Category.assoc, ← (ν i).square.w,
      Category.assoc]
  let g : P ⟶ Q := ⟨fU.hom, gZ.hom, IsPullback.of_horiz_isIso ⟨hfg⟩⟩
  have hgf : g.f = fU.hom := rfl
  have hglocal (i : I) : ν i ≫ g = μ i := FiniteCover.Hom.ext (hμf i) (hg i)
  have hgiso : IsIso g := by
    have : IsIso g.f := inferInstanceAs (IsIso fU.hom)
    have : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift g.f g :=
      CategoryTheory.IsHomLift.map _ g
    have := (isFiberedInGroupoids_finiteCoverProjection (B := B) (S := S) (hS := hS)
      (d := d)).isStronglyCartesian_homLift g.f g
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso
      (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) g.f g
  have hgfibre : Functor.FibreHom (finiteCoverProjection (B := B) (S := S) (hS := hS)
      (d := d)) P Q hP hQ g := by
    refine Functor.fibreHom_of_isHomLift_id hP hQ ?_
    refine CategoryTheory.IsHomLift.of_fac'
      (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) (𝟙 U) g hP' hQ' ?_
    exact hfU.trans (Category.id_comp _).symm
  refine ⟨g, ⟨hgfibre, hgiso, hglocal⟩, ?_⟩
  rintro ψ ⟨hψ, -, hψlocal⟩
  refine FiniteCover.Hom.ext ?_ ?_
  · exact (FiniteCover.Hom.f_eq_of_fibreHom hP' hQ' ψ hψ).trans (hgf.trans hfU).symm
  · refine FiniteHilbert.site_hom_ext (fun i => (ν i).g) hνsource fun i => ?_
    exact (congrArg FiniteCover.Hom.g (hψlocal i)).trans (hg i).symm

/-- **Condition (2) of Stacks 026F for `ℋ_d`: the presheaves `Mor(x, y)` of Stacks 02ZB on the
localized sites are sheaves.** For every object `W` of the big fppf site and objects `x` and `y`
of the fibre of `ℋ_d` over `W`, the presheaf `Mor(x, y)` on the site over `W` is a sheaf. -/
theorem isMorSheaf_finiteCoverProjection :
    letI : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsFibered :=
      Functor.IsFiberedInGroupoids.isFibered
        (isFiberedInGroupoids_finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d))
    ∀ (W : BigFppfOver B S hS)
      (x y : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber W),
      Functor.IsMorSheaf (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d))
        (BigFppfOver.topology B S hS) W x y := by
  let : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsFibered :=
    Functor.IsFiberedInGroupoids.isFibered
      (isFiberedInGroupoids_finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d))
  exact fun W x y =>
    Functor.isMorSheaf_of_isomIsSheaf
      (isFiberedInGroupoids_finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d))
      (fun a b ha hb _ V g hg Vij pr₁ pr₂ hVij ar br arij brij =>
        isom_isSheaf_finiteCoverProjection a b ha hb V g hg Vij pr₁ pr₂ hVij ar br arij brij)
      W x y

end AlgebraicGeometry.Stack

end
