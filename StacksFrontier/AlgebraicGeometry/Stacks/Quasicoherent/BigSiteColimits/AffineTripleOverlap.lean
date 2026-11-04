module

public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCokernelDescent

/-!
# The triple self-product of a covering morphism of affine objects

Descent along a single covering morphism `h : W ⟶ U` of a site runs through the first two
differentials of the Čech complex of the one-element covering `{h}`, whose terms are the sections
over `W`, over a double self-product `V` of `W` over `U` and over a triple self-product `V₃`.
`PresheafOfModules.cechDiff₀` and `PresheafOfModules.cechDiff₁` are the two differentials, and
`PresheafOfModules.cechDiff₁_eq_amitsurDiff₁` identifies the second with the degree-one Amitsur
differential as soon as the sections over `V₃` are the base change of the sections over `U` along
the ring of global functions on `V₃`.  Both differentials take the objects `V` and `V₃` and the
five projections between them as data: nothing produces them, and in particular nothing says that
a triple self-product of an affine object over an affine object is again affine or computes its
ring of global functions.

This file produces them.  The triple self-product is built as `W ×_U (W ×_U W)`, so that its ring
of global functions comes out in the right-associated spelling `B ⊗[A] (B ⊗[A] B)` the Amitsur
complex is written in, and its five projections are obtained from the universal property of the
double product.  Affineness is the pairwise statement
`AlgebraicGeometry.FibredSite.isAffineOver_pullback` applied twice, and the ring of global
functions is the pairwise pushout identification applied twice.

The pairwise identification has to be redone here rather than reused, and the reason is the whole
difficulty of a *self*-product.  `AlgebraicGeometry.algebra_isPushout_appTop_of_isPullback`
concludes `Algebra.IsPushout Γ(Z, ⊤) Γ(X, ⊤) Γ(Y, ⊤) Γ(Pb, ⊤)`, which mentions the two ring maps
`Γ(X, ⊤) → Γ(Pb, ⊤)` and `Γ(Y, ⊤) → Γ(Pb, ⊤)` as the instances `Algebra Γ(X, ⊤) Γ(Pb, ⊤)` and
`Algebra Γ(Y, ⊤) Γ(Pb, ⊤)`.  For a self-product `X` and `Y` are the same scheme, so those are one
instance and not two, and the statement no longer says what it says for `X ≠ Y`: it asserts that
the single map induces an isomorphism from the tensor product, which is false.  The two
projections of a self-product are genuinely different maps out of the same ring, so they must be
explicit arguments.  Accordingly the identification below is stated for two given algebra maps
`u` and `v`, with the pushout square taken in `CommRingCat`, where the two legs are morphisms and
not instances, and the conclusion is an algebra equivalence out of the tensor product rather than
`Algebra.IsPushout`.

## Main definitions

* `CommRingCat.ringEquivTensorProductOfIsPushout` and
  `CommRingCat.algEquivTensorProductOfIsPushout`: **a pushout square of commutative rings whose
  two legs out of the base are the structure maps identifies the vertex with the tensor product**,
  the two maps into the vertex being given as algebra maps rather than as instances, so that the
  two may have the same source.
* `AlgebraicGeometry.algEquivTensorAppTopOfIsPullback`: **the ring of global functions on a fibre
  product of affine schemes is the tensor product of those of the two factors over that of the
  base**, in the same two-explicit-maps form.
* `AlgebraicGeometry.algEquivTensorAppTopOfIsPullback₃`: the same for an iterated fibre product
  `X₁ ×_Z (X₂ ×_Z X₃)` of three affine schemes over an affine one.

## Main results

* `CategoryTheory.IsPullback.exists_cechProjections`: **the three projections of a triple
  self-product onto the double self-product**, with the three identifications of their composites
  with the two projections of the double product, which are exactly the equations
  `PresheafOfModules.cechDiff₁_cechDiff₀_apply` asks for.
* `AlgebraicGeometry.FibredSite.isPullback_toScheme_of_isPullback`: a fibre product square of a
  slice of the fppf site associated with a category fibred in groupoids is carried to a fibre
  product square of schemes.
* `AlgebraicGeometry.FibredSite.isAffineOver_of_isPullback` and
  `AlgebraicGeometry.FibredSite.isAffineOver_of_isPullback₃`: **a fibre product of two, or of
  three, affine objects of a slice over an affine object is affine**, with the squares as
  hypotheses so that the slice need not be asserted to have fibre products.
* `AlgebraicGeometry.FibredSite.exists_affine_triple_self_product`: **a covering morphism between
  affine objects of a slice has an affine double and an affine triple self-product**, with the two
  projections, the three projections onto the double product, the two fibre product squares and
  the four commutations the Čech differentials consume.
* `AlgebraicGeometry.FibredSite.algEquivTensorGammaOfIsPullback` and
  `AlgebraicGeometry.FibredSite.algEquivTensorGammaOfIsPullback₃`: **the ring of global functions
  on a fibre product of two, or of three, affine objects of a slice is the tensor product of those
  of the factors over that of the object they lie over.**

## Implementation notes

The whole chain is stated for fibre product *squares* rather than for the chosen fibre product of a
pair of morphisms, following `AlgebraicGeometry.FibredSite.algebra_isPushout_gamma_of_isPullback`:
a caller holding two morphisms produces the square from `CategoryTheory.IsPullback.of_hasPullback`
and `AlgebraicGeometry.BigFppfOver.hasPullbacks_of_isFiberedInGroupoids`, while a caller holding a
square already — as the triple product does, its outer square being over the composite `V ⟶ W ⟶ U`
and not over a chosen pullback — uses it directly.

`AlgebraicGeometry.FibredSite.exists_affine_triple_self_product` returns the two objects, the five
projections, the affineness, the two squares and the four commutations in one existential rather
than in several: the later equations speak of the same projections the earlier ones do, and an
existentially quantified morphism cannot be handed to a separate statement.

The algebra structures on the rings of global functions are the caller's own throughout,
identified with the maps induced by the morphisms by hypothesis, so that the conclusions are about
the caller's tensor products; no instance is created here.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 0238](https://stacks.math.columbia.edu/tag/0238)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u v w t

namespace CategoryTheory.IsPullback

variable {C : Type t} [Category.{v} C]

/-- **The three projections of a triple self-product onto the double self-product.**  Let
`q₁, q₂ : V ⟶ W` be the two projections of a double self-product of `W` over `U`, and let `V₃` be
the fibre product of `W` and `V` over `U`, the map `V ⟶ U` being `q₁` followed by the covering
morphism.  Then `V₃` is a triple self-product of `W` over `U`, and the projection `t₂₃` onto `V`
is accompanied by two further maps `t₁₂` and `t₁₃` to `V` pairing the first projection of `V₃`
onto `W` with the second and with the third.

The four conclusions are the identifications of the three projections of `V₃` onto `W`: `t₁₂ ≫ q₁`
and `t₁₃ ≫ q₁` are both the first, `t₁₂ ≫ q₂` and `t₂₃ ≫ q₁` are both the second, and `t₁₃ ≫ q₂`
and `t₂₃ ≫ q₂` are both the third.  These are exactly the hypotheses of
`PresheafOfModules.cechDiff₁_cechDiff₀_apply`. -/
theorem exists_cechProjections {U W V V₃ : C} {h : W ⟶ U} {q₁ q₂ : V ⟶ W}
    (hV : IsPullback q₁ q₂ h h) {pr₁ : V₃ ⟶ W} {t₂₃ : V₃ ⟶ V}
    (hV₃ : IsPullback pr₁ t₂₃ h (q₁ ≫ h)) :
    ∃ t₁₂ t₁₃ : V₃ ⟶ V, t₁₂ ≫ q₁ = pr₁ ∧ t₁₃ ≫ q₁ = pr₁ ∧
      t₁₂ ≫ q₂ = t₂₃ ≫ q₁ ∧ t₁₃ ≫ q₂ = t₂₃ ≫ q₂ := by
  have h12 : pr₁ ≫ h = (t₂₃ ≫ q₁) ≫ h := by rw [Category.assoc, hV₃.w]
  have h13 : pr₁ ≫ h = (t₂₃ ≫ q₂) ≫ h := by rw [Category.assoc, ← hV.w, hV₃.w]
  exact ⟨hV.lift pr₁ (t₂₃ ≫ q₁) h12, hV.lift pr₁ (t₂₃ ≫ q₂) h13, hV.lift_fst .., hV.lift_fst ..,
    hV.lift_snd .., hV.lift_snd ..⟩

end CategoryTheory.IsPullback

namespace CommRingCat

variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra A D] (u : B →ₐ[A] D) (v : C →ₐ[A] D)
  (h : IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (algebraMap A C))
    (CommRingCat.ofHom (u : B →+* D)) (CommRingCat.ofHom (v : C →+* D)))

/-- **A pushout square of commutative rings whose two legs out of the base are the structure maps
identifies the vertex with the tensor product.**  The tensor product sits in such a square
(`CommRingCat.isPushout_tensorProduct`), and two vertices of pushout squares on one cospan are
isomorphic.

The two maps into the vertex are the algebra maps `u` and `v` rather than the instances
`Algebra B D` and `Algebra C D`, which is what makes the statement usable when `B` and `C` are the
same ring: a self-product has two different projections, and as instances they would be one. -/
noncomputable def ringEquivTensorProductOfIsPushout : B ⊗[A] C ≃+* D :=
  ((CommRingCat.isPushout_tensorProduct A B C).isoPushout ≪≫
    h.isoPushout.symm).commRingCatIsoToRingEquiv

/-- `CommRingCat.ringEquivTensorProductOfIsPushout` is the comparison with the chosen pushout
followed by the inverse of the given one. -/
lemma ringEquivTensorProductOfIsPushout_apply (y : B ⊗[A] C) :
    ringEquivTensorProductOfIsPushout u v h y = h.isoPushout.inv.hom
      ((CommRingCat.isPushout_tensorProduct A B C).isoPushout.hom.hom y) := rfl

/-- Two pushout squares on one cospan are compared through the chosen pushout compatibly with
both legs. -/
private theorem comp_isoPushout_hom_inv {R S T P Q : CommRingCat} {f : R ⟶ S} {g : R ⟶ T}
    {i₁ : S ⟶ P} {i₂ : T ⟶ P} {j₁ : S ⟶ Q} {j₂ : T ⟶ Q} (hP : IsPushout f g i₁ i₂)
    (hQ : IsPushout f g j₁ j₂) :
    i₁ ≫ hP.isoPushout.hom ≫ hQ.isoPushout.inv = j₁ ∧
      i₂ ≫ hP.isoPushout.hom ≫ hQ.isoPushout.inv = j₂ := by
  simp

/-- `CommRingCat.ringEquivTensorProductOfIsPushout` restricted to the left factor is `u`. -/
lemma ringEquivTensorProductOfIsPushout_tmul_one (b : B) :
    ringEquivTensorProductOfIsPushout u v h (b ⊗ₜ[A] 1) = u b := by
  rw [ringEquivTensorProductOfIsPushout_apply]
  exact congr($((comp_isoPushout_hom_inv _ h).1).hom b)

/-- `CommRingCat.ringEquivTensorProductOfIsPushout` restricted to the right factor is `v`. -/
lemma ringEquivTensorProductOfIsPushout_one_tmul (c : C) :
    ringEquivTensorProductOfIsPushout u v h ((1 : B) ⊗ₜ[A] c) = v c := by
  rw [ringEquivTensorProductOfIsPushout_apply]
  exact congr($((comp_isoPushout_hom_inv _ h).2).hom c)

/-- `CommRingCat.ringEquivTensorProductOfIsPushout` on a pure tensor. -/
lemma ringEquivTensorProductOfIsPushout_tmul (b : B) (c : C) :
    ringEquivTensorProductOfIsPushout u v h (b ⊗ₜ[A] c) = u b * v c := by
  have hbc : b ⊗ₜ[A] c = (b ⊗ₜ[A] (1 : C)) * ((1 : B) ⊗ₜ[A] c) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hbc, map_mul, ringEquivTensorProductOfIsPushout_tmul_one,
    ringEquivTensorProductOfIsPushout_one_tmul]

/-- `CommRingCat.ringEquivTensorProductOfIsPushout` as an equivalence of algebras over the base of
the pushout square. -/
noncomputable def algEquivTensorProductOfIsPushout : B ⊗[A] C ≃ₐ[A] D :=
  AlgEquiv.ofRingEquiv (f := ringEquivTensorProductOfIsPushout u v h) fun a => by
    rw [Algebra.TensorProduct.algebraMap_apply, ringEquivTensorProductOfIsPushout_tmul_one,
      AlgHom.commutes]

/-- `CommRingCat.algEquivTensorProductOfIsPushout` on a pure tensor. -/
lemma algEquivTensorProductOfIsPushout_tmul (b : B) (c : C) :
    algEquivTensorProductOfIsPushout u v h (b ⊗ₜ[A] c) = u b * v c :=
  ringEquivTensorProductOfIsPushout_tmul u v h b c

end CommRingCat

namespace AlgebraicGeometry

/-- **The ring of global functions on a fibre product of affine schemes is the tensor product of
the rings of global functions of the two factors over that of the base**, with the two maps out of
the factors given explicitly.  This is
`AlgebraicGeometry.isPushout_appTop_of_isPullback` read through
`CommRingCat.algEquivTensorProductOfIsPushout`.

Unlike `AlgebraicGeometry.algebra_isPushout_appTop_of_isPullback` the two maps into the global
functions on the fibre product are not instances, so the two factors are allowed to be the same
scheme; `hu` and `hv` say that they are compatible with the structure map of the base, which is
all that is needed, the maps themselves being those of the two projections. -/
noncomputable def algEquivTensorAppTopOfIsPullback {X Y Z Pb : Scheme.{u}} [IsAffine X]
    [IsAffine Y] [IsAffine Z] {fst : Pb ⟶ X} {snd : Pb ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g)
    [Algebra Γ(Z, ⊤) Γ(X, ⊤)] [Algebra Γ(Z, ⊤) Γ(Y, ⊤)] [Algebra Γ(Z, ⊤) Γ(Pb, ⊤)]
    (hf : algebraMap Γ(Z, ⊤) Γ(X, ⊤) = f.appTop.hom)
    (hg : algebraMap Γ(Z, ⊤) Γ(Y, ⊤) = g.appTop.hom)
    (hu : ∀ a, fst.appTop.hom (algebraMap Γ(Z, ⊤) Γ(X, ⊤) a) = algebraMap Γ(Z, ⊤) Γ(Pb, ⊤) a)
    (hv : ∀ a, snd.appTop.hom (algebraMap Γ(Z, ⊤) Γ(Y, ⊤) a) = algebraMap Γ(Z, ⊤) Γ(Pb, ⊤) a) :
    Γ(X, ⊤) ⊗[Γ(Z, ⊤)] Γ(Y, ⊤) ≃ₐ[Γ(Z, ⊤)] Γ(Pb, ⊤) := by
  refine CommRingCat.algEquivTensorProductOfIsPushout
    (AlgHom.mk fst.appTop.hom hu) (AlgHom.mk snd.appTop.hom hv) ?_
  rw [hf, hg]
  simpa using isPushout_appTop_of_isPullback h

/-- `AlgebraicGeometry.algEquivTensorAppTopOfIsPullback` on a pure tensor: the product of the two
restrictions along the projections. -/
lemma algEquivTensorAppTopOfIsPullback_tmul {X Y Z Pb : Scheme.{u}} [IsAffine X]
    [IsAffine Y] [IsAffine Z] {fst : Pb ⟶ X} {snd : Pb ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g)
    [Algebra Γ(Z, ⊤) Γ(X, ⊤)] [Algebra Γ(Z, ⊤) Γ(Y, ⊤)] [Algebra Γ(Z, ⊤) Γ(Pb, ⊤)]
    (hf : algebraMap Γ(Z, ⊤) Γ(X, ⊤) = f.appTop.hom)
    (hg : algebraMap Γ(Z, ⊤) Γ(Y, ⊤) = g.appTop.hom)
    (hu : ∀ a, fst.appTop.hom (algebraMap Γ(Z, ⊤) Γ(X, ⊤) a) = algebraMap Γ(Z, ⊤) Γ(Pb, ⊤) a)
    (hv : ∀ a, snd.appTop.hom (algebraMap Γ(Z, ⊤) Γ(Y, ⊤) a) = algebraMap Γ(Z, ⊤) Γ(Pb, ⊤) a)
    (b : Γ(X, ⊤)) (c : Γ(Y, ⊤)) :
    algEquivTensorAppTopOfIsPullback h hf hg hu hv (b ⊗ₜ[Γ(Z, ⊤)] c) =
      fst.appTop.hom b * snd.appTop.hom c :=
  CommRingCat.algEquivTensorProductOfIsPushout_tmul _ _ _ b c

/-- **The ring of global functions on an iterated fibre product `X₁ ×_Z (X₂ ×_Z X₃)` of affine
schemes over an affine one is the right-associated triple tensor product.**  The two squares are
the inner fibre product `X₂ ×_Z X₃` and the outer one over the composite `X₂ ×_Z X₃ ⟶ X₂ ⟶ Z`, and
the conclusion is the pairwise identification applied to each, the inner one tensored with
`Γ(X₁, ⊤)`.

The right-associated spelling is the one the Amitsur complex of `Module.Descent` is written in, so
no associativity comparison is needed between this and
`Module.Descent.amitsurInsert₁`, `Module.Descent.amitsurInsert₂` and
`Module.Descent.amitsurInsert₃`. -/
noncomputable def algEquivTensorAppTopOfIsPullback₃ {X₁ X₂ X₃ Z Pb Pb₃ : Scheme.{u}}
    [IsAffine X₁] [IsAffine X₂] [IsAffine X₃] [IsAffine Z] [IsAffine Pb]
    {f₁ : X₁ ⟶ Z} {f₂ : X₂ ⟶ Z} {f₃ : X₃ ⟶ Z}
    {fst : Pb ⟶ X₂} {snd : Pb ⟶ X₃} (h : IsPullback fst snd f₂ f₃)
    {fst₃ : Pb₃ ⟶ X₁} {snd₃ : Pb₃ ⟶ Pb} (h₃ : IsPullback fst₃ snd₃ f₁ (fst ≫ f₂))
    [Algebra Γ(Z, ⊤) Γ(X₁, ⊤)] [Algebra Γ(Z, ⊤) Γ(X₂, ⊤)] [Algebra Γ(Z, ⊤) Γ(X₃, ⊤)]
    [Algebra Γ(Z, ⊤) Γ(Pb, ⊤)] [Algebra Γ(Z, ⊤) Γ(Pb₃, ⊤)]
    (hf₁ : algebraMap Γ(Z, ⊤) Γ(X₁, ⊤) = f₁.appTop.hom)
    (hf₂ : algebraMap Γ(Z, ⊤) Γ(X₂, ⊤) = f₂.appTop.hom)
    (hf₃ : algebraMap Γ(Z, ⊤) Γ(X₃, ⊤) = f₃.appTop.hom)
    (hfst : algebraMap Γ(Z, ⊤) Γ(Pb, ⊤) = (fst ≫ f₂).appTop.hom)
    (hfst₃ : algebraMap Γ(Z, ⊤) Γ(Pb₃, ⊤) = (fst₃ ≫ f₁).appTop.hom)
    (hsnd₃ : algebraMap Γ(Z, ⊤) Γ(Pb₃, ⊤) = (snd₃ ≫ fst ≫ f₂).appTop.hom) :
    Γ(X₁, ⊤) ⊗[Γ(Z, ⊤)] (Γ(X₂, ⊤) ⊗[Γ(Z, ⊤)] Γ(X₃, ⊤)) ≃ₐ[Γ(Z, ⊤)] Γ(Pb₃, ⊤) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl (R := Γ(Z, ⊤)) (A₁ := Γ(X₁, ⊤)))
      (algEquivTensorAppTopOfIsPullback h hf₂ hf₃
        (fun a => by rw [hf₂, hfst, Scheme.Hom.comp_appTop]; rfl)
        (fun a => by rw [hf₃, hfst, h.w, Scheme.Hom.comp_appTop]; rfl))).trans
    (algEquivTensorAppTopOfIsPullback h₃ hf₁ hfst
      (fun a => by rw [hf₁, hfst₃, Scheme.Hom.comp_appTop]; rfl)
      (fun a => by rw [hfst, hsnd₃, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]; rfl))

/-- `AlgebraicGeometry.algEquivTensorAppTopOfIsPullback₃` on a pure tensor: the product of the
three restrictions along the three projections onto the factors. -/
lemma algEquivTensorAppTopOfIsPullback₃_tmul {X₁ X₂ X₃ Z Pb Pb₃ : Scheme.{u}}
    [IsAffine X₁] [IsAffine X₂] [IsAffine X₃] [IsAffine Z] [IsAffine Pb]
    {f₁ : X₁ ⟶ Z} {f₂ : X₂ ⟶ Z} {f₃ : X₃ ⟶ Z}
    {fst : Pb ⟶ X₂} {snd : Pb ⟶ X₃} (h : IsPullback fst snd f₂ f₃)
    {fst₃ : Pb₃ ⟶ X₁} {snd₃ : Pb₃ ⟶ Pb} (h₃ : IsPullback fst₃ snd₃ f₁ (fst ≫ f₂))
    [Algebra Γ(Z, ⊤) Γ(X₁, ⊤)] [Algebra Γ(Z, ⊤) Γ(X₂, ⊤)] [Algebra Γ(Z, ⊤) Γ(X₃, ⊤)]
    [Algebra Γ(Z, ⊤) Γ(Pb, ⊤)] [Algebra Γ(Z, ⊤) Γ(Pb₃, ⊤)]
    (hf₁ : algebraMap Γ(Z, ⊤) Γ(X₁, ⊤) = f₁.appTop.hom)
    (hf₂ : algebraMap Γ(Z, ⊤) Γ(X₂, ⊤) = f₂.appTop.hom)
    (hf₃ : algebraMap Γ(Z, ⊤) Γ(X₃, ⊤) = f₃.appTop.hom)
    (hfst : algebraMap Γ(Z, ⊤) Γ(Pb, ⊤) = (fst ≫ f₂).appTop.hom)
    (hfst₃ : algebraMap Γ(Z, ⊤) Γ(Pb₃, ⊤) = (fst₃ ≫ f₁).appTop.hom)
    (hsnd₃ : algebraMap Γ(Z, ⊤) Γ(Pb₃, ⊤) = (snd₃ ≫ fst ≫ f₂).appTop.hom)
    (b₁ : Γ(X₁, ⊤)) (b₂ : Γ(X₂, ⊤)) (b₃ : Γ(X₃, ⊤)) :
    algEquivTensorAppTopOfIsPullback₃ h h₃ hf₁ hf₂ hf₃ hfst hfst₃ hsnd₃
        (b₁ ⊗ₜ[Γ(Z, ⊤)] (b₂ ⊗ₜ[Γ(Z, ⊤)] b₃)) =
      fst₃.appTop.hom b₁ * ((snd₃ ≫ fst).appTop.hom b₂ * (snd₃ ≫ snd).appTop.hom b₃) := by
  simp only [algEquivTensorAppTopOfIsPullback₃, AlgEquiv.trans_apply,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, AlgEquiv.coe_refl, id_eq,
    AlgEquiv.coe_toAlgHom, algEquivTensorAppTopOfIsPullback_tmul, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, map_mul]

end AlgebraicGeometry

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

include hS in
/-- **A fibre product square of a slice of the associated fppf site is carried to a fibre product
square of schemes.**  The projection of the slice carries it to a fibre product square of `𝒳`, a
cospan being a connected shape; the structure functor carries that to a fibre product square of
the big fppf category, every morphism of a category fibred in groupoids being strongly cartesian;
and the functor to schemes preserves fibre products. -/
theorem isPullback_toScheme_of_isPullback (hp : p.IsFiberedInGroupoids) {x : 𝒳}
    {W Y Z Pb : Over x} {fst : Pb ⟶ Y} {snd : Pb ⟶ Z} {f : Y ⟶ W} {g : Z ⟶ W}
    (h : IsPullback fst snd f g) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (p.map fst.left))
      ((BigFppfOver.toScheme B S hS).map (p.map snd.left))
      ((BigFppfOver.toScheme B S hS).map (p.map f.left))
      ((BigFppfOver.toScheme B S hS).map (p.map g.left)) :=
  (Functor.IsFiberedInGroupoids.map_isPullback p hp f.left g.left _ _
    (h.map (Over.forget x))).map (BigFppfOver.toScheme B S hS)

include hS in
/-- **The fibre product of two affine objects of a slice of the associated fppf site over an
affine object is affine.**  This is
`AlgebraicGeometry.FibredSite.isAffineOver_pullback` with the fibre product square as a hypothesis
instead of being the chosen fibre product of two morphisms, which is the form an iterated fibre
product needs: the outer square of a triple product is over a composite, not over a chosen
pullback. -/
theorem isAffineOver_of_isPullback (hp : p.IsFiberedInGroupoids) {x : 𝒳} {W Y Z Pb : Over x}
    {fst : Pb ⟶ Y} {snd : Pb ⟶ Z} {f : Y ⟶ W} {g : Z ⟶ W} (h : IsPullback fst snd f g)
    (hW : IsAffineOver B S hS (p.obj W.left)) (hY : IsAffineOver B S hS (p.obj Y.left))
    (hZ : IsAffineOver B S hS (p.obj Z.left)) :
    IsAffineOver B S hS (p.obj Pb.left) := by
  have key {X : Over x} (hX : IsAffineOver B S hS (p.obj X.left)) :
      IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj X.left)) := hX
  have _ := key hW
  have _ := key hY
  have _ := key hZ
  exact IsAffine.of_isIso (isPullback_toScheme_of_isPullback B S hS p hp h).isoPullback.hom

include hS in
/-- **An iterated fibre product of three affine objects of a slice of the associated fppf site
over an affine object is affine**, the inner square being the fibre product of the last two
factors and the outer one that of the first factor with it. -/
theorem isAffineOver_of_isPullback₃ (hp : p.IsFiberedInGroupoids) {x : 𝒳}
    {W Y Z T Pb Pb₃ : Over x} {fst : Pb ⟶ Z} {snd : Pb ⟶ T} {g : Z ⟶ W} {k : T ⟶ W}
    (h : IsPullback fst snd g k) {f : Y ⟶ W} {fst₃ : Pb₃ ⟶ Y} {snd₃ : Pb₃ ⟶ Pb}
    (h₃ : IsPullback fst₃ snd₃ f (fst ≫ g))
    (hW : IsAffineOver B S hS (p.obj W.left)) (hY : IsAffineOver B S hS (p.obj Y.left))
    (hZ : IsAffineOver B S hS (p.obj Z.left)) (hT : IsAffineOver B S hS (p.obj T.left)) :
    IsAffineOver B S hS (p.obj Pb₃.left) :=
  isAffineOver_of_isPullback B S hS p hp h₃ hW hY
    (isAffineOver_of_isPullback B S hS p hp h hW hZ hT)

include hS in
/-- **A covering morphism between affine objects of a slice of the associated fppf site has an
affine double and an affine triple self-product**, and they come with the two projections of the
double product, the three projections of the triple product onto the double one, the two fibre
product squares that compute their rings of global functions, and the four commutations the two
Čech differentials consume: `q₁ ≫ h = q₂ ≫ h` for `PresheafOfModules.cechDiff₀_restrictₛₗ` and the
three identifications of the projections onto the covering object for
`PresheafOfModules.cechDiff₁_cechDiff₀_apply`.

The triple product is `W ×_U (W ×_U W)`, built as the fibre product of the covering morphism with
the first projection of the double product followed by the covering morphism, so that its ring of
global functions is `B ⊗[A] (B ⊗[A] B)` in the right-associated spelling of the Amitsur complex.
Everything is returned together because the equations speak of the same morphisms. -/
theorem exists_affine_triple_self_product (hp : p.IsFiberedInGroupoids) {x : 𝒳} {U W : Over x}
    (h : W ⟶ U) (hU : IsAffineOver B S hS (p.obj U.left))
    (hW : IsAffineOver B S hS (p.obj W.left)) :
    ∃ (V V₃ : Over x) (q₁ q₂ : V ⟶ W) (t₁₂ t₁₃ t₂₃ : V₃ ⟶ V),
      IsAffineOver B S hS (p.obj V.left) ∧ IsAffineOver B S hS (p.obj V₃.left) ∧
      IsPullback q₁ q₂ h h ∧ IsPullback (t₁₂ ≫ q₁) t₂₃ h (q₁ ≫ h) ∧
      q₁ ≫ h = q₂ ≫ h ∧ t₁₂ ≫ q₁ = t₁₃ ≫ q₁ ∧ t₁₂ ≫ q₂ = t₂₃ ≫ q₁ ∧
      t₁₃ ≫ q₂ = t₂₃ ≫ q₂ := by
  have _ : HasPullbacks 𝒳 := BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS p hp
  have hV : IsPullback (pullback.fst h h) (pullback.snd h h) h h := IsPullback.of_hasPullback h h
  have hV₃ : IsPullback (pullback.fst h (pullback.fst h h ≫ h))
      (pullback.snd h (pullback.fst h h ≫ h)) h (pullback.fst h h ≫ h) :=
    IsPullback.of_hasPullback h (pullback.fst h h ≫ h)
  obtain ⟨t₁₂, t₁₃, h₁, h₂, h₃, h₄⟩ := hV.exists_cechProjections hV₃
  have hVaff := isAffineOver_of_isPullback B S hS p hp hV hU hW hW
  refine ⟨pullback h h, pullback h (pullback.fst h h ≫ h), pullback.fst h h, pullback.snd h h,
    t₁₂, t₁₃, pullback.snd h (pullback.fst h h ≫ h), hVaff,
    isAffineOver_of_isPullback B S hS p hp hV₃ hU hW hVaff, hV, ?_, hV.w, ?_, h₃, h₄⟩
  · rwa [h₁]
  · rw [h₁, h₂]

include hS in
/-- **The ring of global functions on a fibre product of two affine objects of a slice of the
associated fppf site is the tensor product of those of the two factors over that of the object
they lie over**, with the two maps out of the factors given explicitly rather than as instances,
so that the two factors may be the same object.

This is `AlgebraicGeometry.algEquivTensorAppTopOfIsPullback` transported along
`AlgebraicGeometry.FibredSite.isPullback_toScheme_of_isPullback`.  It is the self-product-aware
companion of `AlgebraicGeometry.FibredSite.algebra_isPushout_gamma_of_isPullback`, whose
`Algebra.IsPushout` conclusion identifies the two maps into the fibre product when the two factors
coincide. -/
noncomputable def algEquivTensorGammaOfIsPullback (hp : p.IsFiberedInGroupoids) {x : 𝒳}
    {W Y D Pb : Over x} {fst : Pb ⟶ Y} {snd : Pb ⟶ D} {f : Y ⟶ W} {g : D ⟶ W}
    (h : IsPullback fst snd f g)
    (hW : IsAffineOver B S hS (p.obj W.left)) (hY : IsAffineOver B S hS (p.obj Y.left))
    (hD : IsAffineOver B S hS (p.obj D.left))
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj Y.left), ⊤)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj D.left), ⊤)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj Pb.left), ⊤)]
    (hf : algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj Y.left), ⊤) =
      ((BigFppfOver.toScheme B S hS).map (p.map f.left)).appTop.hom)
    (hg : algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj D.left), ⊤) =
      ((BigFppfOver.toScheme B S hS).map (p.map g.left)).appTop.hom)
    (hu : ∀ a, ((BigFppfOver.toScheme B S hS).map (p.map fst.left)).appTop.hom
        (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj (p.obj Y.left), ⊤) a) =
      algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj Pb.left), ⊤) a)
    (hv : ∀ a, ((BigFppfOver.toScheme B S hS).map (p.map snd.left)).appTop.hom
        (algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj (p.obj D.left), ⊤) a) =
      algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj Pb.left), ⊤) a) :
    Γ((BigFppfOver.toScheme B S hS).obj (p.obj Y.left), ⊤)
        ⊗[Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)]
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj D.left), ⊤)
        ≃ₐ[Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)]
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj Pb.left), ⊤) :=
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj W.left)) := hW
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj Y.left)) := hY
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj D.left)) := hD
  algEquivTensorAppTopOfIsPullback (isPullback_toScheme_of_isPullback B S hS p hp h) hf hg hu hv

include hS in
/-- **The ring of global functions on an iterated fibre product of three affine objects of a slice
of the associated fppf site over an affine object is the right-associated triple tensor product of
those of the three factors over that of the object they lie over.**

This is `AlgebraicGeometry.algEquivTensorAppTopOfIsPullback₃` transported along
`AlgebraicGeometry.FibredSite.isPullback_toScheme_of_isPullback`, and the two factors of the inner
fibre product and the outer factor are allowed to be one and the same object, which is the case
the Čech complex of a one-element covering needs: there the three factors are three copies of the
covering object, the triple tensor product is the degree-two term of the Amitsur complex of the
ring of global functions on it over that of the object covered, and the three projections onto the
factors induce `Module.Descent.amitsurInsert₁`, `Module.Descent.amitsurInsert₂` and
`Module.Descent.amitsurInsert₃` after base change. -/
noncomputable def algEquivTensorGammaOfIsPullback₃ (hp : p.IsFiberedInGroupoids) {x : 𝒳}
    {W Y₁ Y₂ Y₃ Pb Pb₃ : Over x} {f₁ : Y₁ ⟶ W} {f₂ : Y₂ ⟶ W} {f₃ : Y₃ ⟶ W}
    {fst : Pb ⟶ Y₂} {snd : Pb ⟶ Y₃} (h : IsPullback fst snd f₂ f₃)
    {fst₃ : Pb₃ ⟶ Y₁} {snd₃ : Pb₃ ⟶ Pb} (h₃ : IsPullback fst₃ snd₃ f₁ (fst ≫ f₂))
    (hW : IsAffineOver B S hS (p.obj W.left)) (hY₁ : IsAffineOver B S hS (p.obj Y₁.left))
    (hY₂ : IsAffineOver B S hS (p.obj Y₂.left)) (hY₃ : IsAffineOver B S hS (p.obj Y₃.left))
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj Y₁.left), ⊤)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj Y₂.left), ⊤)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj Y₃.left), ⊤)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj Pb.left), ⊤)]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj Pb₃.left), ⊤)]
    (hf₁ : algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj Y₁.left), ⊤) =
      ((BigFppfOver.toScheme B S hS).map (p.map f₁.left)).appTop.hom)
    (hf₂ : algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj Y₂.left), ⊤) =
      ((BigFppfOver.toScheme B S hS).map (p.map f₂.left)).appTop.hom)
    (hf₃ : algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj Y₃.left), ⊤) =
      ((BigFppfOver.toScheme B S hS).map (p.map f₃.left)).appTop.hom)
    (hfst : algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj Pb.left), ⊤) =
      (((BigFppfOver.toScheme B S hS).map (p.map fst.left)) ≫
        ((BigFppfOver.toScheme B S hS).map (p.map f₂.left))).appTop.hom)
    (hfst₃ : algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj Pb₃.left), ⊤) =
      (((BigFppfOver.toScheme B S hS).map (p.map fst₃.left)) ≫
        ((BigFppfOver.toScheme B S hS).map (p.map f₁.left))).appTop.hom)
    (hsnd₃ : algebraMap Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj Pb₃.left), ⊤) =
      (((BigFppfOver.toScheme B S hS).map (p.map snd₃.left)) ≫
        ((BigFppfOver.toScheme B S hS).map (p.map fst.left)) ≫
        ((BigFppfOver.toScheme B S hS).map (p.map f₂.left))).appTop.hom) :
    Γ((BigFppfOver.toScheme B S hS).obj (p.obj Y₁.left), ⊤)
        ⊗[Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)]
      (Γ((BigFppfOver.toScheme B S hS).obj (p.obj Y₂.left), ⊤)
          ⊗[Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)]
        Γ((BigFppfOver.toScheme B S hS).obj (p.obj Y₃.left), ⊤))
        ≃ₐ[Γ((BigFppfOver.toScheme B S hS).obj (p.obj W.left), ⊤)]
      Γ((BigFppfOver.toScheme B S hS).obj (p.obj Pb₃.left), ⊤) :=
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj W.left)) := hW
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj Y₁.left)) := hY₁
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj Y₂.left)) := hY₂
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj Y₃.left)) := hY₃
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj Pb.left)) :=
    isAffineOver_of_isPullback B S hS p hp h hW hY₂ hY₃
  have hpb₃ : IsPullback ((BigFppfOver.toScheme B S hS).map (p.map fst₃.left))
      ((BigFppfOver.toScheme B S hS).map (p.map snd₃.left))
      ((BigFppfOver.toScheme B S hS).map (p.map f₁.left))
      ((BigFppfOver.toScheme B S hS).map (p.map fst.left) ≫
        (BigFppfOver.toScheme B S hS).map (p.map f₂.left)) := by
    have htr := isPullback_toScheme_of_isPullback B S hS p hp h₃
    rwa [Over.comp_left, Functor.map_comp, Functor.map_comp] at htr
  algEquivTensorAppTopOfIsPullback₃ (isPullback_toScheme_of_isPullback B S hS p hp h) hpb₃
    hf₁ hf₂ hf₃ hfst hfst₃ hsnd₃

end AlgebraicGeometry.FibredSite

end
