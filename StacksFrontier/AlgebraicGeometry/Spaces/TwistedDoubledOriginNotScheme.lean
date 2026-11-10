module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedDoubledOriginZeroFibre

/-!
# The twisted doubled origin is not a scheme

The fourth assertion of the example is that `X = U/R` is not a scheme.  If it were, its
local ring at the origin would be a local domain with fraction field `k(x)`, with `x` in the
maximal ideal and residue field `K`, which is impossible.

The argument formalized here is the functorial form of that: a scheme `Y` over
`S = Spec k[x]` representing `X` receives a map from the chart `U`, which must coincide with
its Galois twist on the punctured chart because the two are identified in the quotient.  The
chart is reduced and irreducible and the puncture is dense in it, so the two maps already
agree on the fibre over the origin.  That fibre of `X` is `Spec K` by
`AlgebraicGeometry.TwistedDoubledOrigin.twistedRelationQuotient_zeroFibre`, so representing
it produces a `k`-algebra endomorphism of `K` whose image is fixed by `σ`; as that
endomorphism is bijective, `σ` is the identity, contradicting the hypothesis.

## Main results

* `AlgebraicGeometry.TwistedDoubledOrigin.quadraticGaloisTwistedDoubledOrigin_not_representable`:
  the quotient sheaf is not isomorphic to the functor of points of any scheme over the base.

## Implementation notes

Representability is taken in the strongest reasonable sense: the representing object may be
an arbitrary scheme over the base, not merely an object of the chosen size-bounded site.  The
two lemmas `agree_near_of_dense` and
`AlgebraicGeometry.TwistedDoubledOrigin.comp_eq_of_dense_of_subsingleton` are the standard
fact that two morphisms out of a reduced scheme which agree on a dense open and at a point
agree on a neighbourhood of that point, in the form needed here.  The second is not private:
the closing claim of the example, that the descent datum relative to
`{Spec k' ⟶ Spec k}` is not effective, uses it for the same purpose, to compare the two sheets
of the doubled line at the origin.

## References

* [Stacks Project, Tag 03FN](https://stacks.math.columbia.edu/tag/03FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.TwistedDoubledOrigin

/-- Two morphisms out of a reduced scheme which agree on a dense open subscheme and at a
point agree on a neighbourhood of that point. -/
private theorem agree_near_of_dense {X Y : Scheme.{u}} [IsReduced X] (f g : X ⟶ Y)
    (D : X.Opens) (hD : Dense (D : Set X)) (hfg : D.ι ≫ f = D.ι ≫ g) (x : X)
    (hx : f x = g x) : ∃ V : X.Opens, x ∈ V ∧ V.ι ≫ f = V.ι ≫ g := by
  obtain ⟨A, hA, hxA, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (x := f x) (U := ⊤) (show f x ∈ (⊤ : Y.Opens) from trivial)
  let V := f ⁻¹ᵁ A ⊓ g ⁻¹ᵁ A
  have hxV : x ∈ V := ⟨hxA, by
    change g x ∈ A
    rwa [← hx]⟩
  have : IsAffine A := hA
  let W : V.toScheme.Opens := V.ι ⁻¹ᵁ D
  have hW : Dense (W : Set V.toScheme) := hD.preimage V.ι.isOpenEmbedding.isOpenMap
  have : IsDominant W.ι := Opens.isDominant_ι hW
  have hf : W.ι ≫ f.resLE A V inf_le_left = W.ι ≫ g.resLE A V inf_le_right := by
    apply (cancel_mono A.ι).mp
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
    simpa only [← Category.assoc, morphismRestrict_ι] using
      congrArg ((V.ι ∣_ D) ≫ ·) hfg
  refine ⟨V, hxV, ?_⟩
  simpa using congrArg (· ≫ A.ι) (ext_of_isDominant W.ι hf)

/-- Two morphisms out of a reduced scheme which agree on a dense open subscheme agree after
composing with a morphism from a scheme with one point which lands where they agree. -/
theorem comp_eq_of_dense_of_subsingleton {X Y T : Scheme.{u}} [IsReduced X]
    [Subsingleton T] (f g : X ⟶ Y) (D : X.Opens) (hD : Dense (D : Set X))
    (hfg : D.ι ≫ f = D.ι ≫ g) (z : T ⟶ X) (t : T) (hx : f (z t) = g (z t)) :
    z ≫ f = z ≫ g := by
  obtain ⟨V, hv, he⟩ := agree_near_of_dense f g D hD hfg (z t) hx
  have hrange : Set.range z ⊆ Set.range V.ι := by
    rintro _ ⟨t', rfl⟩
    rw [Scheme.Opens.range_ι]
    change z t' ∈ V
    simpa only [Subsingleton.elim t' t] using hv
  let l := IsOpenImmersion.lift V.ι z hrange
  have hl : l ≫ V.ι = z := IsOpenImmersion.lift_fac _ _ _
  simpa only [← Category.assoc, hl] using congrArg (fun a => l ≫ a) he

/-- A natural transformation out of a representable presheaf restricted along a full functor
is the restriction of a morphism. -/
private theorem natTrans_from_restricted_yoneda {C : Type v} [Category.{u} C] {D : Type w}
    [Category.{u} D] (F : C ⥤ D) [F.Full] (U : C) (Y : D)
    (q : F.op ⋙ yoneda.obj (F.obj U) ⟶ F.op ⋙ yoneda.obj Y) :
    ∃ f : F.obj U ⟶ Y, q = F.op.whiskerLeft (yoneda.map f) := by
  refine ⟨q.app (op U) (𝟙 _), ?_⟩
  ext T a
  simpa using q.naturality_apply (F.preimage a).op (𝟙 (F.obj U))

/-- The chart belongs to a big fppf site containing the base. -/
private theorem cover_mem_site (k K : Type u) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] (B : BigFppfSite.{u}) (hS : B.Contains (base k)) :
    B.Contains (cover K) := by
  let z := Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : k)))
  have : IsClosedImmersion z :=
    IsClosedImmersion.spec_of_surjective _ (Polynomial.eval_surjective 0)
  have hk : (Spec (.of k)).size < B.cutoff :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact z hS
  exact Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit k
    (Polynomial K) hk

/-- Composition of morphisms between spectra of commutative rings, in terms of ring maps. -/
private theorem spec_map_comp_eq_iff {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (h : A →+* C) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom h) ↔ g.comp f = h := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Spec.map_injective.eq_iff]
  exact ⟨fun H => congrArg CommRingCat.Hom.hom H, fun H => congrArg CommRingCat.ofHom H⟩

/-- **Stacks 03FN.** The quotient `X = U/R` is not represented by a scheme over the base. -/
@[stacks 03FN "not_scheme"]
theorem quadraticGaloisTwistedDoubledOrigin_not_representable (k K : Type u) [Field k]
    [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) (hσ : σ ≠ 1) (B : BigFppfSite.{u})
    (hS : B.Contains (base k))
    [HasSheafify (BigFppfOver.topology B (base k) hS) (Type u)] :
    ¬ ∃ Y : Over (base k),
      Nonempty ((quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS).obj ≅
        Stacks.Groupoids.points (Over.post B.inclusion) Y) := by
  classical
  rintro ⟨Y, ⟨e⟩⟩
  let S := base k
  let C := BigFppfOver B S hS
  let F := Over.post (X := B.obj hS) B.inclusion
  let P : Over S ⥤ (Cᵒᵖ ⥤ Type u) := yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj F.op
  let U := coverOverBase k K
  let Z := zeroCoverOverBase k K
  let Z₀ := zeroBaseOverBase k
  let D : U.left.Opens := puncturedCover K
  let j := twistedRelation k K σ
  let Q := (quadraticGaloisTwistedDoubledOrigin k K hdegree σ hσ B hS).obj
  let q : P.obj U ⟶ Q := Stacks.Groupoids.toQuotientSheaf _ F j
  have hU := cover_mem_site k K B hS
  let U' : C := Over.mk (ObjectProperty.homMk (coverMap k K) : B.obj hU ⟶ B.obj hS)
  obtain ⟨f, hf⟩ := natTrans_from_restricted_yoneda F U' Y (q ≫ e.hom)
  change U ⟶ Y at f
  change q ≫ e.hom = P.map f at hf
  let γ : U ⟶ U := Over.homMk (galoisAction k K σ) (by
    dsimp [U, coverOverBase, galoisAction, coverMap]
    rw [spec_map_comp_eq_iff]
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp)
  have hDmem : B.Contains D.toScheme := Scheme.size_lt_of_isOpenImmersion D.ι hU
  let V' : C := Over.mk (ObjectProperty.homMk (D.ι ≫ U.hom) : B.obj hDmem ⟶ B.obj hS)
  let r : F.obj V' ⟶ relationOverBase k K := Over.homMk coprod.inr (by
    change coprod.inr ≫ coprod.desc _ _ = D.ι ≫ U.hom
    exact coprod.inr_desc _ _)
  have hrel := congrArg (fun t => t.app (op V') r)
    (Stacks.Groupoids.sourceMap_toQuotientSheaf (BigFppfOver.topology B S hS) F j)
  have hrel' : (q ≫ e.hom).app (op V') (r ≫ j.source) =
      (q ≫ e.hom).app (op V') (r ≫ j.target) := congrArg (e.hom.app (op V')) hrel
  rw [hf] at hrel'
  change (r ≫ j.source) ≫ f = (r ≫ j.target) ≫ f at hrel'
  have hfg : D.ι ≫ f.left = D.ι ≫ γ.left ≫ f.left := by
    have h := congrArg Over.Hom.left hrel'
    change (coprod.inr ≫ j.source.left) ≫ f.left =
      (coprod.inr ≫ j.target.left) ≫ f.left at h
    simp only [j, twistedRelation_source, twistedRelation_target, relationSecond_inr,
      relationFirst_inr] at h
    change (D.ι ≫ γ.left) ≫ f.left = D.ι ≫ f.left at h
    simpa only [Category.assoc] using h.symm
  let z : Z ⟶ U := Over.homMk (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : K))))
    (by
      dsimp [Z, U, zeroCoverOverBase, coverOverBase, coverMap]
      rw [spec_map_comp_eq_iff]
      exact RingHom.ext fun p => Polynomial.eval_map (algebraMap k K) 0)
  let τ : Z ⟶ Z := Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom)) (by
    dsimp [Z, zeroCoverOverBase]
    rw [spec_map_comp_eq_iff]
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp)
  let c : Z ⟶ Z₀ := Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K))) (by
    dsimp [Z, Z₀, zeroCoverOverBase, zeroBaseOverBase]
    rw [spec_map_comp_eq_iff]
    apply Polynomial.ringHom_ext <;> simp)
  have hτz : τ ≫ z = z ≫ γ := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : K))) =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : K))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom σ.toRingEquiv.toRingHom))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext <;> simp
  have hτc : τ ≫ c = c := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      Spec.map (CommRingCat.ofHom (algebraMap k K))
    rw [spec_map_comp_eq_iff]
    ext a
    exact σ.commutes a
  have : PreirreducibleSpace U.left := by
    change PreirreducibleSpace (PrimeSpectrum (Polynomial K)); infer_instance
  have : IsReduced U.left := by
    change IsReduced (Spec (.of (Polynomial K))); infer_instance
  have hD : Dense D.carrier := by
    apply D.isOpen.dense
    refine ⟨⟨⊥, inferInstance⟩, ?_⟩
    exact Polynomial.X_ne_zero
  have : Subsingleton Z.left := by
    change Subsingleton (PrimeSpectrum K); infer_instance
  let t : Z.left := (default : Spec (.of K))
  have hz : z.left ≫ f.left = z.left ≫ (γ.left ≫ f.left) := by
    apply comp_eq_of_dense_of_subsingleton f.left (γ.left ≫ f.left) D hD hfg z.left t
    have h := congrArg (fun m : Z.left ⟶ U.left => m t) (congrArg Over.Hom.left hτz)
    change z.left (τ.left t) = γ.left (z.left t) at h
    change f.left (z.left t) = f.left (γ.left (z.left t))
    congr 1
    simpa only [Subsingleton.elim (τ.left t) t] using h
  have hτzf : τ ≫ z ≫ f = z ≫ f := by
    apply Over.OverMorphism.ext
    have h := congrArg (fun a => a ≫ f.left) (congrArg Over.Hom.left hτz)
    exact h.trans hz.symm
  let a : P.obj Z ⟶ Q := P.map z ≫ q
  have ha : P.map τ ≫ a = a := by
    apply (cancel_mono e.hom).mp
    simp only [a, Category.assoc, hf, ← P.map_comp]
    exact congrArg P.map hτzf
  obtain ⟨e₀⟩ := twistedRelationQuotient_zeroFibre k K σ B hS
  let b : P.obj Z ⟶ P.obj Z := prod.lift a (P.map c) ≫ e₀.hom
  have hb : P.map τ ≫ b = b := by
    dsimp [b]
    rw [← Category.assoc]
    congr 1
    apply prod.hom_ext
    · simpa using ha
    · simp only [Category.assoc, prod.lift_snd, ← P.map_comp, hτc]
  have hzclosed : IsClosedImmersion z.left :=
    IsClosedImmersion.spec_of_surjective _ (Polynomial.eval_surjective 0)
  have hZ : B.Contains Z.left :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact z.left hU
  let T : C := Over.mk (ObjectProperty.homMk Z.hom : B.obj hZ ⟶ B.obj hS)
  obtain ⟨β, hβ⟩ := natTrans_from_restricted_yoneda F T Z b
  change Z ⟶ Z at β
  change b = P.map β at hβ
  have hτβ : τ ≫ β = β := by
    rw [hβ, ← P.map_comp] at hb
    have h := congrArg (fun a => a.app (op T) (𝟙 Z)) hb
    change (𝟙 Z ≫ τ) ≫ β = (𝟙 Z) ≫ β at h
    simpa only [Category.id_comp] using h
  let φ := (Spec.preimage β.left).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = β.left := Spec.map_preimage _
  have hφk : ∀ a, φ (algebraMap k K a) = algebraMap k K a := by
    have hw := β.w
    rw [← hφ] at hw
    change Spec.map (CommRingCat.ofHom φ) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (algebraMap k K) 0)) =
      Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (algebraMap k K) 0)) at hw
    rw [spec_map_comp_eq_iff] at hw
    intro a
    simpa using congrArg (fun t : Polynomial k →+* K => t (Polynomial.C a)) hw
  let ψ : K →ₐ[k] K := { __ := φ, commutes' := hφk }
  have hinvar : ∀ a, σ (φ a) = φ a := by
    have h := congrArg Over.Hom.left hτβ
    change τ.left ≫ β.left = β.left at h
    rw [← hφ] at h
    change Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫
      Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom φ) at h
    rw [spec_map_comp_eq_iff] at h
    intro a
    exact congrArg (fun t : K →+* K => t a) h
  apply hσ
  ext a
  obtain ⟨a, rfl⟩ := ψ.bijective.2 a
  exact hinvar a

end AlgebraicGeometry.TwistedDoubledOrigin

end
