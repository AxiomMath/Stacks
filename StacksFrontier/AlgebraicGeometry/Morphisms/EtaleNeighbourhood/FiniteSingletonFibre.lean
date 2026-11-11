module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.UniquePrimeLocalization
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite morphisms with a singleton fibre

Let `f : X ⟶ Y` be a finite morphism of schemes and let `x` be a point of `X` whose fibre
`f ⁻¹' {f x}` is the singleton `{x}`. Such a point behaves as if `f` were a closed immersion
near `x`: every neighbourhood of `x` contains the inverse image of a neighbourhood of `f x`,
the induced map of local rings is finite — and of finite presentation if `f` is — and the
stalk at `x` of a quasi-coherent module agrees with the stalk at `f x` of its pushforward.

## Main results

* `AlgebraicGeometry.exists_open_preimage_le`: a neighbourhood of `f x` whose inverse image
  lies inside a prescribed neighbourhood of `x`.
* `AlgebraicGeometry.finite_stalkMap_of_preimage_singleton`: the stalk map is finite.
* `AlgebraicGeometry.finitePresentation_stalkMap_of_preimage_singleton`: the stalk map is of
  finite presentation when `f` is.
* `AlgebraicGeometry.exists_linearEquiv_stalkPushforward_of_finite_singleton_fiber`: the
  canonical map from the stalk of the pushforward of a quasi-coherent module to its stalk, with
  scalars restricted along the stalk map, is a linear isomorphism.
* `AlgebraicGeometry.stalk_isomorphic_pushforward_of_finite_singleton_fiber`: the two stalks are
  isomorphic in `ModuleCat`.

## Implementation notes

Neighbourhoods are represented by open subsets containing the specified point, and the fibre
hypothesis is stated on the underlying map of topological spaces. The point of the target is
always taken to be the image `f x` of the chosen source point, so that the auxiliary equality
between the two points disappears from the statements. The local-ring map is the canonical
stalk map `Scheme.Hom.stalkMap`.

For the pushforward statement, the equality of modules in the source is represented by the
canonical map `TopCat.Presheaf.stalkPushforward` being a linear equivalence: the module
structure on the source stalk is restricted from `𝒪_{X,x}` to `𝒪_{Y,f x}` along the stalk
map, and the pushforward is Mathlib's canonical pushforward of modules on schemes.

## References

* [Stacks Project, Tag 05B8](https://stacks.math.columbia.edu/tag/05B8)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- For a finite morphism whose fibre over `y` is the singleton `x`, the inverse image of
some open neighbourhood of `y` is contained in any prescribed open neighbourhood of `x`. -/
@[stacks 05B8 "inverse_image_neighbourhoods"]
lemma exists_open_preimage_le {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (x : X) (y : Y) (hxy : f x = y) (hfiber : f ⁻¹' {y} = {x})
    (U : X.Opens) (hxU : x ∈ U) :
    ∃ V : Y.Opens, y ∈ V ∧ f ⁻¹ᵁ V ≤ U := by
  subst hxy
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp <| f.isClosedMap.comap_nhds_le
    (by rw [hfiber, nhdsSet_singleton]; exact U.isOpen.mem_nhds hxU)
  obtain ⟨W, hWV, hW, hyW⟩ := mem_nhds_iff.mp hV
  exact ⟨⟨W, hW⟩, hyW, fun z hz => hVU (hWV hz)⟩

section FiniteStalkMap

/-- If `q` is the unique prime of a module-finite `A`-algebra `B` over the prime `p` of `A`, then
a ring-hom property that is preserved by localization and respects isomorphisms holds for the
induced map `A_p → B_q` of localizations as soon as it holds for `A → B`. -/
private theorem localRingHom_of_uniquePrime
    (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (hloc : RingHom.LocalizationPreserves @P) (hiso : RingHom.RespectsIso @P)
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] (p : Ideal A) (q : Ideal B) [p.IsPrime] [q.IsPrime]
    (hpq : p = Ideal.comap (algebraMap A B) q)
    (hq : p.primesOver B = {q}) (h : P (algebraMap A B)) :
    P (Localization.localRingHom p q (algebraMap A B) hpq) := by
  let M := p.primeCompl
  let Bp := Localization (Algebra.algebraMapSubmonoid B M)
  let Bq := Localization.AtPrime q
  let : IsLocalization (Algebra.algebraMapSubmonoid B M) Bp := Localization.isLocalization
  let : IsLocalization (Submonoid.map (algebraMap A B) M) Bp := Localization.isLocalization
  let : IsLocalization.AtPrime Bp q := isLocalization_atPrime_of_primesOver_eq_singleton hq Bp
  let e : Bp ≃ₐ[B] Bq := IsLocalization.algEquiv q.primeCompl Bp Bq
  have hcomp : Localization.localRingHom p q (algebraMap A B) hpq =
      e.toRingEquiv.toRingHom.comp (IsLocalization.map Bp (algebraMap A B)
        (Submonoid.le_comap_map M) : Localization.AtPrime p →+* Bp) := by
    apply IsLocalization.ringHom_ext M
    ext a; simp [e, Localization.localRingHom, Bq]
  rw [hcomp]
  exact hiso.1 _ _ (hloc (algebraMap A B) M _ Bp h)

/-- The stalk map of `Spec φ` at a prime `q` whose contraction along `φ` determines `q`
uniquely is a finite ring map. -/
private theorem finite_spec_stalkMap_of_uniqueFiber
    {A B : CommRingCat.{u}} (φ : A ⟶ B) (hφ : φ.hom.Finite)
    (q : PrimeSpectrum B)
    (hq : ∀ r : Ideal B, r.IsPrime →
      Ideal.comap φ.hom r = Ideal.comap φ.hom q.asIdeal → r = q.asIdeal) :
    ((Spec.map φ).stalkMap q).hom.Finite := by
  let : Algebra A B := φ.hom.toAlgebra
  have hAlgMap : algebraMap A B = φ.hom := rfl
  have hmod : Module.Finite A B := RingHom.finite_algebraMap.mp hφ
  let p := q.asIdeal.comap φ.hom
  have hprimes : p.primesOver B = {q.asIdeal} := by
    ext r
    constructor
    · rintro ⟨hr, hLie⟩
      apply hq r hr
      calc
        Ideal.comap φ.hom r = p := by
          rw [← hAlgMap]
          simpa [Ideal.under] using (Ideal.liesOver_iff r p).mp hLie |>.symm
        _ = Ideal.comap φ.hom q.asIdeal := rfl
    · intro hr
      rw [Set.mem_singleton_iff] at hr
      subst r
      refine ⟨q.2, (Ideal.liesOver_iff q.asIdeal p).2 ?_⟩
      simp [Ideal.under, p, hAlgMap]
  have hpq : p = Ideal.comap (algebraMap A B) q.asIdeal := rfl
  have hlocal := localRingHom_of_uniquePrime @RingHom.Finite RingHom.finite_localizationPreserves
    RingHom.finite_respectsIso p q.asIdeal hpq hprimes hφ
  exact (RingHom.finite_respectsIso.arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso φ q)).2 hlocal

/-- The affine case of `AlgebraicGeometry.finite_stalkMap_of_preimage_singleton`, obtained
from the ring-theoretic statement by transporting along `Scheme.isoSpec`. -/
private lemma finite_stalkMap_of_preimage_singleton_affine
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsAffine X] [IsAffine Y]
    (x : X) (hx : f ⁻¹' {f x} = {x}) :
    (f.stalkMap x).hom.Finite := by
  let eX := X.isoSpec
  let eY := Y.isoSpec
  let g : Spec Γ(X, ⊤) ⟶ Spec Γ(Y, ⊤) := eX.inv ≫ f ≫ eY.hom
  let x' : Spec Γ(X, ⊤) := eX.hom x
  have hgpoint : g x' = eY.hom (f x) := by simp [g, x']
  have hxg : g ⁻¹' {g x'} = {x'} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      have hz' : f (eX.inv z) = f x := by
        have hzy : eY.hom (f (eX.inv z)) = eY.hom (f x) := by
          simpa [g, x'] using hz
        have := congrArg eY.inv hzy
        simpa using this
      have hzx : eX.inv z = x := by
        have hmem : eX.inv z ∈ f ⁻¹' {f x} := hz'
        simpa [hx] using hmem
      have := congrArg eX.hom hzx
      simpa [x'] using this
    · rintro rfl
      rfl
  let cY : (Spec Γ(Y, ⊤)).presheaf.stalk (g x') ≅
      (Spec Γ(Y, ⊤)).presheaf.stalk (eY.hom (f x)) :=
    (Spec Γ(Y, ⊤)).presheaf.stalkCongr (.of_eq hgpoint)
  have hMorph : eX.hom ≫ g = f ≫ eY.hom := by
    simp [g]
  have hmapIso : cY.hom ≫ eY.hom.stalkMap (f x) ≫ f.stalkMap x =
      g.stalkMap x' ≫ eX.hom.stalkMap x := by
    have h := Scheme.Hom.stalkMap_congr_hom (eX.hom ≫ g) (f ≫ eY.hom) hMorph x
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at h
    simpa [cY, g, x', Scheme.Hom.stalkMap_comp, Category.assoc] using h.symm
  have hArrow : Arrow.mk (g.stalkMap x') ≅ Arrow.mk (f.stalkMap x) := by
    refine Arrow.isoMk (asIso (cY.hom ≫ eY.hom.stalkMap (f x)))
      (asIso (eX.hom.stalkMap x)) hmapIso
  obtain ⟨φ, hφ⟩ := Spec.map_surjective g
  have hφfinite : φ.hom.Finite := by
    apply (IsFinite.SpecMap_iff φ).mp
    rw [hφ]
    infer_instance
  have hprimeUnique : ∀ r : Ideal Γ(X, ⊤), r.IsPrime →
      Ideal.comap φ.hom r = Ideal.comap φ.hom x'.asIdeal → r = x'.asIdeal := by
    intro r hr hcomap
    let z : Spec Γ(X, ⊤) := ⟨r, hr⟩
    have hpoints : (Spec.map φ) z = (Spec.map φ) x' := by
      apply PrimeSpectrum.ext
      rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal]
      exact hcomap
    have hpoints' : g z = g x' := by simpa [hφ] using hpoints
    have hmem : z ∈ g ⁻¹' {g x'} := hpoints'
    have heq : z = x' := by
      rw [hxg] at hmem
      exact Set.mem_singleton_iff.mp hmem
    simpa [z] using congrArg (fun z : Spec Γ(X, ⊤) => z.asIdeal) heq
  have hmapfinite : ((Spec.map φ).stalkMap x').hom.Finite :=
    finite_spec_stalkMap_of_uniqueFiber φ hφfinite x' hprimeUnique
  have hgfinite : (g.stalkMap x').hom.Finite := by
    rw [← hφ]
    exact hmapfinite
  exact (RingHom.finite_respectsIso.arrow_mk_iso_iff hArrow).mp hgfinite

/-- For a finite morphism with a singleton fibre at `x`, the induced map on the local rings at
`f x` and `x` is finite. -/
@[stacks 05B8 "finite_local_ring_map"]
lemma finite_stalkMap_of_preimage_singleton
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (x : X) (hx : f ⁻¹' {f x} = {x}) :
    (f.stalkMap x).hom.Finite := by
  obtain ⟨U, hU, hfx, -⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (Opens.mem_top (f x))
  let f' := f ∣_ U
  let x' : ↥((f ⁻¹ᵁ U).toScheme) := ⟨x, hfx⟩
  have hx' : f' ⁻¹' {f' x'} = {x'} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      apply Subtype.ext
      have hval : f z.1 = f x := by
        have h : (f' z).1 = (f' x').1 := congrArg Subtype.val hz
        calc
          f z.1 = (f' z).1 := by simp [f', morphismRestrict_base_coe]
          _ = (f' x').1 := h
          _ = f x := by
            change ((f ∣_ U) x').1 = f x
            rw [morphismRestrict_base_coe]
      have hmem : z.1 ∈ f ⁻¹' {f x} := hval
      have hzx : z.1 = x := by simpa [hx] using hmem
      simpa [x'] using hzx
    · rintro rfl
      rfl
  let : IsFinite f' := inferInstance
  let : IsAffine ↑U := hU
  let : IsAffine (↑(f ⁻¹ᵁ U)) := AlgebraicGeometry.isAffine_of_isAffineHom (f := f')
  exact (RingHom.finite_respectsIso.arrow_mk_iso_iff
    (morphismRestrictStalkMap f U x')).1
    (finite_stalkMap_of_preimage_singleton_affine f' x' hx')

end FiniteStalkMap

section FinitePresentationStalkMap

/-- If `q` is the unique prime of `B` over the prime `p` of `A`, and `A → B` is finite and of
finite presentation, then the induced map `A_p → B_q` of localizations is of finite
presentation. -/
private lemma finitePresentation_localRingHom_of_unique_prime
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (g : A →+* B) (p : Ideal A) (q : Ideal B) [p.IsPrime] [q.IsPrime]
    (hAlg : algebraMap A B = g) (hpq : p = q.comap g) (hprimes : p.primesOver B = {q})
    (hfinite : g.Finite) (hfp : g.FinitePresentation) :
    (Localization.localRingHom p q g hpq).FinitePresentation := by
  subst hAlg
  let : Module.Finite A B := RingHom.finite_algebraMap.mp hfinite
  exact localRingHom_of_uniquePrime @RingHom.FinitePresentation
    RingHom.finitePresentation_localizationPreserves RingHom.finitePresentation_respectsIso
    p q hpq hprimes hfp

/-- If a finite morphism of finite presentation has a singleton fibre over
`f x`, its local-ring map at `x` is of finite presentation. -/
@[stacks 05B8 "finitely_presented_local_ring_map"]
lemma finitePresentation_stalkMap_of_preimage_singleton
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (x : X) (hx : f ⁻¹' {f x} = {x}) (hfp : FinitePresentation f) :
    (f.stalkMap x).hom.FinitePresentation := by
  let U := (Y.affineCover.f (Y.affineCover.idx (f x))).opensRange
  let hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hyU : f x ∈ U := Y.affineCover.covers (f x)
  let V := f ⁻¹ᵁ U
  let hV : IsAffineOpen V := hU.preimage f
  have hxV : x ∈ V := by change f x ∈ U; exact hyU
  let p := (hU.primeIdealOf ⟨f x, hyU⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  let A := Y.presheaf.obj (Opposite.op U)
  let B := X.presheaf.obj (Opposite.op V)
  let g := (f.appLE U V le_rfl).hom
  let : Algebra A B := g.toAlgebra
  have hAlg : algebraMap A B = g := RingHom.algebraMap_toAlgebra g
  have hpq : p = q.comap g := by
    simpa [p, q, g] using congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV le_rfl hxV).symm
  have hprimes : p.primesOver B = {q} := by
    ext r
    constructor
    · rintro ⟨hr, hrp⟩
      let z : Spec B := ⟨r, hr⟩
      have hcomap : r.comap g = p := by
        have hunder := hrp.over.symm
        rw [Ideal.under_def, hAlg] at hunder
        exact hunder
      have hspec : Spec.map (f.appLE U V le_rfl) z =
          hU.primeIdealOf ⟨f x, hyU⟩ := by
        change PrimeSpectrum.comap g z = hU.primeIdealOf ⟨f x, hyU⟩
        apply PrimeSpectrum.ext
        rw [PrimeSpectrum.comap_asIdeal]
        simpa [p, g] using hcomap
      have hchart := congrArg (fun k : Spec B ⟶ Y => k z)
        (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV le_rfl)
      have hpoint : f (hV.fromSpec z) = f x := by
        simpa [hspec, hU.fromSpec_primeIdealOf] using hchart.symm
      have hz : hV.fromSpec z = x := by
        simpa [hx] using (show hV.fromSpec z ∈ f ⁻¹' ({f x} : Set Y) from hpoint)
      have hpeq : z = hV.primeIdealOf ⟨x, hxV⟩ := by
        apply hV.fromSpec.isOpenEmbedding.injective
        rw [hz]; exact (hV.fromSpec_primeIdealOf ⟨x, hxV⟩).symm
      simpa [q] using congrArg PrimeSpectrum.asIdeal hpeq
    · intro hr
      have hqr : r = q := by simpa using hr
      subst r
      refine ⟨inferInstance, ⟨?_⟩⟩
      change p = Ideal.comap (algebraMap A B) q
      simpa [hAlg] using hpq
  let : LocallyOfFinitePresentation f := hfp.locallyOfFinitePresentation
  have hlocal := finitePresentation_localRingHom_of_unique_prime g p q hAlg hpq hprimes
    (by simpa [g, Scheme.Hom.app_eq_appLE] using f.finite_app U hU)
    (f.finitePresentation_appLE hU hV le_rfl)
  exact (RingHom.finitePresentation_respectsIso.arrow_mk_iso_iff
    (IsAffineOpen.arrowStalkMapIso f U hU V hV le_rfl hxV)).2 hlocal

end FinitePresentationStalkMap

section PushforwardStalk

/-- For a finite morphism with a singleton fibre at `x`, the canonical map from the stalk of a
pushforward presheaf of abelian groups to the stalk of the presheaf itself is an isomorphism:
the neighbourhoods of `f x` pulled back to `X` are cofinal among the neighbourhoods of `x`. -/
private lemma stalkPushforward_iso_of_finite_singleton_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (x : X) (hfiber : f ⁻¹' ({f x} : Set Y) = {x})
    (G : TopCat.Presheaf Ab X) :
    IsIso (G.stalkPushforward Ab f.base x) := by
  let H := OpenNhds.map f.base x
  have : H.Initial := by
    rw [Functor.initial_iff_of_isCofiltered]
    constructor
    · intro U
      obtain ⟨V, hyV, hVU⟩ :=
        exists_open_preimage_le f x (f x) rfl hfiber U.1 U.2
      exact ⟨⟨V, hyV⟩, ⟨homOfLE hVU⟩⟩
    · intro d c s s'
      exact ⟨c, 𝟙 _, Subsingleton.elim _ _⟩
  let : H.op.Final := Functor.final_op_of_initial H
  convert! (Functor.Final.colimitIso H.op
    ((OpenNhds.inclusion x).op ⋙ G)).isIso_hom
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU ↦
    (TopCat.Presheaf.stalkPushforward_germ _ f.base G _ x hU).trans ?_
  symm
  exact Limits.colimit.ι_pre ((OpenNhds.inclusion x).op ⋙ G) H.op _

/-- The module structure on a stalk of an `𝒪`-module, read off from the module structure on
the stalks of the underlying presheaf of modules. -/
private noncomputable abbrev stalkModule {Z : Scheme.{u}} (M : Z.Modules) (z : Z) :
    Module ↑(Z.presheaf.stalk z) ↑(M.presheaf.stalk z) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := Z.presheaf) M.val z

/-- The canonical map from a stalk of a pushforward to the corresponding stalk of the original
module carries the germ of a section to the germ of the same section. -/
private lemma germ_stalkPushforward_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (x : X) (W : Y.Opens) (hW : f x ∈ W)
    (s : Γ((Scheme.Modules.pushforward f).obj F, W)) :
    ConcreteCategory.hom (TopCat.Presheaf.stalkPushforward Ab f.base F.presheaf x)
        (((Scheme.Modules.pushforward f).obj F).presheaf.germ W (f x) hW s) =
      F.presheaf.germ (f ⁻¹ᵁ W) x hW s :=
  ConcreteCategory.congr_hom
    (TopCat.Presheaf.stalkPushforward_germ Ab f.base F.presheaf W x hW) s

/-- The canonical map from a stalk of a pushforward to the corresponding stalk of the original
module is linear over the local ring of the target: both scalar actions are computed on germs
of sections, where they agree by the definition of the pushforward. -/
private lemma stalkPushforward_smul {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (x : X) :
    letI := stalkModule F x
    letI := stalkModule ((Scheme.Modules.pushforward f).obj F) (f x)
    letI : Module ↑(Y.presheaf.stalk (f x)) ↑(F.presheaf.stalk x) :=
      Module.compHom _ (f.stalkMap x).hom
    ∀ (m : ↑(Y.presheaf.stalk (f x)))
      (z : ↑(((Scheme.Modules.pushforward f).obj F).presheaf.stalk (f x))),
      ConcreteCategory.hom (TopCat.Presheaf.stalkPushforward Ab f.base F.presheaf x) (m • z) =
        m • ConcreteCategory.hom
          (TopCat.Presheaf.stalkPushforward Ab f.base F.presheaf x) z := by
  let := stalkModule F x
  let := stalkModule ((Scheme.Modules.pushforward f).obj F) (f x)
  let : Module ↑(Y.presheaf.stalk (f x)) ↑(F.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  intro m z
  obtain ⟨U₁, hU₁, ms, hm⟩ := TopCat.Presheaf.exists_germ_eq Y.presheaf m
  obtain ⟨U₂, hU₂, zs, hz⟩ := TopCat.Presheaf.exists_germ_eq
    ((Scheme.Modules.pushforward f).obj F).presheaf (x := f x) z
  let W : Y.Opens := U₁ ⊓ U₂
  have hW : f x ∈ W := ⟨hU₁, hU₂⟩
  have hWX : x ∈ f ⁻¹ᵁ W := hW
  let i₁ : W ⟶ U₁ := homOfLE inf_le_left
  let i₂ : W ⟶ U₂ := homOfLE inf_le_right
  have hm' : Y.presheaf.germ W (f x) hW (Y.presheaf.map i₁.op ms) = m := by
    rw [TopCat.Presheaf.germ_res_apply Y.presheaf i₁ (f x) hW ms]; exact hm
  have hz' : ((Scheme.Modules.pushforward f).obj F).presheaf.germ W (f x) hW
      (((Scheme.Modules.pushforward f).obj F).presheaf.map i₂.op zs) = z := by
    rw [TopCat.Presheaf.germ_res_apply
      ((Scheme.Modules.pushforward f).obj F).presheaf i₂ (f x) hW zs]
    exact hz
  have hgsG : ∀ (r : Γ(Y, W)) (s : Γ((Scheme.Modules.pushforward f).obj F, W)),
      ((Scheme.Modules.pushforward f).obj F).presheaf.germ W (f x) hW (r • s) =
        Y.presheaf.germ W (f x) hW r •
          ((Scheme.Modules.pushforward f).obj F).presheaf.germ W (f x) hW s :=
    fun _ _ => PresheafOfModules.germ_smul _ _ _ _ _ _
  have hgsF : ∀ (r : Γ(X, f ⁻¹ᵁ W)) (s : Γ(F, f ⁻¹ᵁ W)),
      F.presheaf.germ (f ⁻¹ᵁ W) x hWX (r • s) =
        X.presheaf.germ (f ⁻¹ᵁ W) x hWX r • F.presheaf.germ (f ⁻¹ᵁ W) x hWX s :=
    fun _ _ => PresheafOfModules.germ_smul _ _ _ _ _ _
  set r : Γ(Y, W) := Y.presheaf.map i₁.op ms with hr
  set t : Γ((Scheme.Modules.pushforward f).obj F, W) :=
    ((Scheme.Modules.pushforward f).obj F).presheaf.map i₂.op zs with ht
  rw [← hm', ← hz', ← hgsG r t, germ_stalkPushforward_apply,
    germ_stalkPushforward_apply]
  change F.presheaf.germ (f ⁻¹ᵁ W) x hWX (r • t) =
    (f.stalkMap x).hom (Y.presheaf.germ W (f x) hW r) • F.presheaf.germ (f ⁻¹ᵁ W) x hWX t
  rw [Scheme.Hom.germ_stalkMap_apply f W x hW r, ← hgsF (f.app W r) t]
  rfl

/-- Let `f : X ⟶ Y` be finite and suppose that the fibre over `f x` is the singleton `{x}`.
For a quasi-coherent `O_X`-module `F` we have `F_x = (f_* F)_{f x}` as `O_{Y,f x}`-modules:
the canonical map `TopCat.Presheaf.stalkPushforward` from the stalk of `f_* F` at `f x` to the
stalk of `F` at `x` (sending the germ of a section over `V` to the germ of the same section
over `f ⁻¹ V`) is an `O_{Y,f x}`-linear isomorphism, where `O_{Y,f x}` acts on `F_x` through
the stalk map. The statement provides a linear equivalence whose underlying function is this
canonical map. -/
@[stacks 05B8 "pushforward_stalk"]
theorem exists_linearEquiv_stalkPushforward_of_finite_singleton_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (x : X) (hfiber : f ⁻¹' ({f x} : Set Y) = {x})
    (F : X.Modules) [F.IsQuasicoherent] :
    letI : Module (X.presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    letI : Module (Y.presheaf.stalk (f x))
        ↑(TopCat.Presheaf.stalk F.val.presheaf x) :=
      Module.compHom _ (f.stalkMap x).hom
    letI : Module (Y.presheaf.stalk (f x))
        ↑(TopCat.Presheaf.stalk
          ((Scheme.Modules.pushforward f).obj F).val.presheaf (f x)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Y.presheaf) ((Scheme.Modules.pushforward f).obj F).val (f x)
    ∃ e : ↑(TopCat.Presheaf.stalk
          ((Scheme.Modules.pushforward f).obj F).val.presheaf (f x)) ≃ₗ[Y.presheaf.stalk (f x)]
        ↑(TopCat.Presheaf.stalk F.val.presheaf x),
      ⇑e = ConcreteCategory.hom
        (TopCat.Presheaf.stalkPushforward Ab f.base F.val.presheaf x) := by
  let := stalkModule F x
  let := stalkModule ((Scheme.Modules.pushforward f).obj F) (f x)
  let : Module ↑(Y.presheaf.stalk (f x)) ↑(F.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  let := stalkPushforward_iso_of_finite_singleton_fiber f x hfiber F.presheaf
  let e := asIso (TopCat.Presheaf.stalkPushforward Ab f.base F.presheaf x)
  let lin : ↑(((Scheme.Modules.pushforward f).obj F).presheaf.stalk (f x)) →ₗ[
        Y.presheaf.stalk (f x)] ↑(F.presheaf.stalk x) :=
    { toFun := ConcreteCategory.hom e.hom
      map_add' := map_add (ConcreteCategory.hom e.hom)
      map_smul' := stalkPushforward_smul f F x }
  exact ⟨LinearEquiv.ofBijective lin (ConcreteCategory.bijective_of_isIso e.hom), rfl⟩

/-- Let `f : X ⟶ Y` be finite and suppose that the fibre over `f x` is the
singleton `{x}`. For a quasi-coherent `O_X`-module `F`, its stalk at `x`, viewed
as an `O_{Y,f x}`-module, is isomorphic to the stalk at `f x` of `f_* F`.

This only records that some isomorphism exists; the form of Stacks Tag 05B8 (4) naming the
canonical comparison map is `exists_linearEquiv_stalkPushforward_of_finite_singleton_fiber`. -/
theorem stalk_isomorphic_pushforward_of_finite_singleton_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (x : X) (hfiber : f ⁻¹' ({f x} : Set Y) = {x})
    (F : X.Modules) [F.IsQuasicoherent] :
    letI : Module (X.presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    letI : Module (Y.presheaf.stalk (f x))
        ↑(TopCat.Presheaf.stalk F.val.presheaf x) :=
      Module.compHom _ (f.stalkMap x).hom
    letI : Module (Y.presheaf.stalk (f x))
        ↑(TopCat.Presheaf.stalk
          ((Scheme.Modules.pushforward f).obj F).val.presheaf (f x)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Y.presheaf) ((Scheme.Modules.pushforward f).obj F).val (f x)
    Nonempty
      (ModuleCat.of (Y.presheaf.stalk (f x))
          ↑(TopCat.Presheaf.stalk F.val.presheaf x) ≅
        ModuleCat.of (Y.presheaf.stalk (f x))
          ↑(TopCat.Presheaf.stalk
            ((Scheme.Modules.pushforward f).obj F).val.presheaf (f x))) := by
  obtain ⟨e, -⟩ := exists_linearEquiv_stalkPushforward_of_finite_singleton_fiber f x hfiber F
  exact ⟨e.symm.toModuleIso⟩

end PushforwardStalk

end AlgebraicGeometry
