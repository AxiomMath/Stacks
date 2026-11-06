module

public import StacksFrontier.AlgebraicGeometry.FlagTower.Tower
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFromBasis
public import StacksFrontier.AlgebraicGeometry.Recovery27.GrassmannianScheme

/-!
# The partial flag variety as a tower over `X × G(l, n)` and over `X`

Let `X` be a scheme, `0 ≤ l < n` and `m = n - l`. The partial flag variety of `𝒪_X^n` is a
composition of projective space bundles in two ways, and this file identifies them over `X`.
This is the scheme-theoretic, `γ`-free, step of the proof of [Stacks, Tag 0FIQ].

* **Tower B over `X`**: `Stacks.FlagTower.tower m 𝒪_X^n`, the tower `𝐏(ℰ^{(m-1)}) ⟶ ⋯ ⟶
  𝐏(𝒪^n) ⟶ X` built on the successive tautological kernels. Its points over `f : T ⟶ X` are the
  flags `K₀ ⊇ ⋯ ⊇ K_{m-1}` of `𝒪_T^n` with `𝒪_T^n / K_i` finite locally free of rank `i + 1`.
* **Tower A over `X × G(l, n)`**: `Stacks.FlagTower.tower m 𝒬`, where `𝒬` is the universal
  quotient `𝒪^n ↠ 𝒬` of rank `m` on the Grassmannian `G(l, n)_X` of `X`
  (`AlgebraicGeometry.Grassmannian.schemeOver l n X = X ×_{Spec ℤ} G(l, n)`). Its points over a
  point `h : T ⟶ G(l, n)_X` are the flags of length `m` of `h^*𝒬`.

The two are identified by pulling a flag of `h^*𝒬` back along `𝒪_T^n ↠ h^*𝒬`
(`Stacks.FlagTower.Flag.comap`): the last member of the result is the kernel of the quotient,
which recovers the point `h` of the Grassmannian, and the other members are the preimages of the
flag. Conversely the last member `K_{m-1}` of a flag of `𝒪_T^n` has a cokernel of rank `m`, a
point of `G(l, n)`, and the flag is the preimage of its image in that cokernel. The
identification is natural in `T`, so by the Yoneda lemma it is an isomorphism of schemes over
`X` (`Stacks.FlagTower.flagTowerIso`).

## Main definitions

* `Stacks.FlagTower.comapSub`, `Stacks.FlagTower.Flag.comap`: pulling subobjects and flags back
  along an epimorphism.
* `Stacks.FlagTower.grassmannianPointsEquiv`: morphisms into `G(l, n)` are points of the
  Grassmannian functor.
* `Stacks.FlagTower.universalQuotient`: the universal quotient presentation on `G(l, n)_X`.
* `Stacks.FlagTower.flagTowerIso`: **the isomorphism, over `X`, between tower A over
  `G(l, n)_X` and tower B over `X`.**

## References

* [Stacks Project, Tag 0FIQ](https://stacks.math.columbia.edu/tag/0FIQ)
* [Stacks Project, Tag 089S](https://stacks.math.columbia.edu/tag/089S)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.FlagTower

/-! ### Pulling subobjects back along an epimorphism -/

section Comap

variable {T : Scheme.{u}} {M Q : T.Modules} (π : M ⟶ Q) [Epi π]

/-- **The preimage of a subobject `S` of `Q` along an epimorphism `π : M ⟶ Q`**, as the kernel
of `M ⟶ Q ⟶ Q / S`. -/
def comapSub (S : Subobject Q) : Subobject M :=
  kernelSubobject (π ≫ cokernel.π S.arrow)

/-- The preimage has the same cokernel as `S`. -/
def cokernelComapSubIso (S : Subobject Q) :
    cokernel (comapSub π S).arrow ≅ cokernel S.arrow :=
  kernelSubobjectCokernelIso (π ≫ cokernel.π S.arrow)

/-- The preimage of `S` has a cokernel finite locally free of rank `r` exactly when `S` has. -/
theorem rank_comapSub_iff (S : Subobject Q) (r : ℕ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (cokernel (comapSub π S).arrow) r ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (cokernel S.arrow) r :=
  ⟨fun h => AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (cokernelComapSubIso π S) h,
    fun h => AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (cokernelComapSubIso π S).symm h⟩

/-- Kernels of equal morphisms are equal subobjects. -/
theorem kernelSubobject_congr {L : T.Modules} {p p' : M ⟶ L} (h : p = p') :
    kernelSubobject p = kernelSubobject p' := by
  subst h; rfl

/-- Composing with a monomorphism does not change the kernel subobject. -/
private theorem kernelSubobject_eq_of_comp_eq {L L' : T.Modules} {p : M ⟶ L} {p' : M ⟶ L'}
    (g : L ⟶ L') [Mono g] (h : p ≫ g = p') : kernelSubobject p = kernelSubobject p' := by
  subst h; exact (kernelSubobject_comp_mono p g).symm

omit [Epi π] in
set_option synthInstance.maxHeartbeats 400000 in
/-- Taking preimages along `π` is monotone. -/
theorem comapSub_mono {S S' : Subobject Q} (h : S ≤ S') : comapSub π S ≤ comapSub π S' :=
  (kernelSubobject_comp_le (π ≫ cokernel.π S.arrow) _).trans_eq
    (kernelSubobject_congr (by
      rw [Category.assoc, cokernel.π_desc]
      rw [← Subobject.ofLE_arrow h, Category.assoc, cokernel.condition, comp_zero]))

/-- The kernel of `p` lies in that of `p'` exactly when `p'` factors through `p`. -/
theorem exists_desc_of_kernelSubobject_le {L L' : T.Modules} {p : M ⟶ L} {p' : M ⟶ L'} [Epi p]
    (h : kernelSubobject p ≤ kernelSubobject p') : ∃ d : L ⟶ L', p ≫ d = p' := by
  have w : kernel.ι p ≫ p' = 0 := by
    rw [← kernelSubobject_arrow' p, ← Subobject.ofLE_arrow h, Category.assoc, Category.assoc,
      kernelSubobject_arrow_comp, comp_zero, comp_zero]
  exact ⟨Abelian.epiDesc p p' w, Abelian.comp_epiDesc _ _ _⟩

/-- Preimages along an epimorphism reflect the order. -/
theorem le_of_comapSub_le {S S' : Subobject Q} (h : comapSub π S ≤ comapSub π S') : S ≤ S' := by
  obtain ⟨d, hd⟩ := exists_desc_of_kernelSubobject_le h
  rw [Category.assoc] at hd
  have hd' : cokernel.π S.arrow ≫ d = cokernel.π S'.arrow := (cancel_epi π).mp hd
  calc S = kernelSubobject (cokernel.π S.arrow) := (kernelSubobject_cokernel_π S).symm
    _ ≤ kernelSubobject (cokernel.π S.arrow ≫ d) := kernelSubobject_comp_le _ _
    _ = kernelSubobject (cokernel.π S'.arrow) := kernelSubobject_congr hd'
    _ = S' := kernelSubobject_cokernel_π S'

/-- Preimages along an epimorphism preserve and reflect the order. -/
theorem comapSub_le_comapSub_iff {S S' : Subobject Q} : comapSub π S ≤ comapSub π S' ↔ S ≤ S' :=
  ⟨le_of_comapSub_le π, comapSub_mono π⟩

/-- Taking preimages along an epimorphism is injective. -/
theorem comapSub_injective : Function.Injective (comapSub π) := fun _ _ h =>
  le_antisymm (le_of_comapSub_le π h.le) (le_of_comapSub_le π h.ge)

omit [Epi π] in
/-- The preimage of `⊥` is the kernel of `π`. -/
theorem comapSub_bot : comapSub π ⊥ = kernelSubobject π := by
  have : Mono (cokernel.π (⊥ : Subobject Q).arrow) := by
    rw [Subobject.bot_arrow]
    infer_instance
  exact kernelSubobject_comp_mono _ _

/-- **Every subobject containing the kernel of `π` is a preimage.** -/
theorem exists_comapSub_eq {K : Subobject M} (h : kernelSubobject π ≤ K) :
    ∃ S : Subobject Q, comapSub π S = K := by
  have h' : kernelSubobject π ≤ kernelSubobject (cokernel.π K.arrow) := by
    rwa [kernelSubobject_cokernel_π]
  obtain ⟨d, hd⟩ := exists_desc_of_kernelSubobject_le h'
  have : Epi d := epi_of_epi_fac hd
  refine ⟨kernelSubobject d, ?_⟩
  obtain ⟨α, hα⟩ := exists_iso_of_kernelSubobject_eq (cokernel.π (kernelSubobject d).arrow) d
    (kernelSubobject_cokernel_π _)
  exact (kernelSubobject_eq_of_comp_eq α.hom (by rw [Category.assoc, hα, hd])).trans
    (kernelSubobject_cokernel_π K)

/-- A subobject of a module of rank `r` whose cokernel also has rank `r` is `⊥`. -/
theorem eq_bot_of_rank {S : Subobject Q} (r : ℕ)
    (hQ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q r)
    (hS : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (cokernel S.arrow) r) : S = ⊥ := by
  have hE := shortExact_arrow_cokernel S
  have h₁ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (S : T.Modules) :=
    Stacks.FiniteLocallyFree.isFiniteLocallyFree_X₁_of_shortExact _ hE
        (@AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
            _ _ _ _ _ _ Q r hQ)
        (@AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
            _ _ _ _ _ _ _ r hS)
  have h0 := Stacks.Conormal.isFiniteLocallyFreeOfRank_X₁_of_shortExact _ hE r r h₁ hQ hS
  rw [Nat.sub_self] at h0
  have hz : IsZero (S : T.Modules) := @Stacks.Chow.isZero_of_isFiniteLocallyFreeOfRank_zero _ _ h0
  rw [← Subobject.mk_arrow S, Subobject.mk_eq_bot_iff_zero]
  exact hz.eq_of_src _ _

/-- **The preimage of a flag along an epimorphism.** -/
def Flag.comap {m : ℕ} (F : Flag Q m) : Flag M m where
  sub i := comapSub π (F.sub i)
  antitone _ _ h := comapSub_mono π (F.antitone h)
  rank i := (rank_comapSub_iff π _ _).mpr (F.rank i)

/-- The members of the preimage of a flag are the preimages of its members. -/
@[simp]
theorem Flag.comap_sub {m : ℕ} (F : Flag Q m) (i : Fin m) :
    (Flag.comap π F).sub i = comapSub π (F.sub i) :=
  rfl

/-- Pulling flags back along an epimorphism is injective. -/
theorem Flag.comap_injective {m : ℕ} : Function.Injective (Flag.comap (m := m) π) :=
  fun _ _ h => Flag.ext (funext fun i =>
    comapSub_injective π (congrArg (fun H : Flag M m => H.sub i) h))

end Comap

/-! ### Base change of preimages -/

section ComapPullback

variable {T T' : Scheme.{u}} (k : T' ⟶ T)

/-- **The base change of a subobject with locally free cokernel is the kernel of the base
changed cokernel map.** -/
theorem mk_pullback_arrow_eq_kernelSubobject {M : T.Modules} {M' : T'.Modules}
    (e : M' ≅ (Scheme.Modules.pullback k).obj M) (S : Subobject M) (r : ℕ)
    (hS : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (cokernel S.arrow) r) :
    haveI := mono_pullback_map_arrow k S r hS
    Subobject.mk ((Scheme.Modules.pullback k).map S.arrow ≫ e.inv) =
      kernelSubobject (e.hom ≫ (Scheme.Modules.pullback k).map (cokernel.π S.arrow)) := by
  have := mono_pullback_map_arrow k S r hS
  have hE := shortExact_map_pullback_of_isLocallyFree k (shortExact_arrow_cokernel S)
    (isLocallyFree_of_rank hS)
  refine mk_eq_kernelSubobject_of_shortExact (w := by
    rw [Category.assoc, Iso.inv_hom_id_assoc, ← CategoryTheory.Functor.map_comp,
      cokernel.condition, CategoryTheory.Functor.map_zero]) ?_
  refine ShortComplex.shortExact_of_iso ?_ hE
  exact ShortComplex.isoMk (Iso.refl _) e.symm (Iso.refl _) (by simp) (by simp)

/-- **Preimages commute with base change.** Let `π : M ⟶ Q` and `π' : M' ⟶ Q'` be epimorphisms
on `T` and `T'`, identified along `k : T' ⟶ T` by `M' ≅ k^*M` and `Q' ≅ k^*Q` compatibly with
`π`, `π'`. Then the preimage along `π'` of the base change of a flag of `Q` is the base change of
its preimage along `π`. -/
theorem Flag.comap_pullback {M Q : T.Modules} {M' Q' : T'.Modules} (π : M ⟶ Q) [Epi π]
    (π' : M' ⟶ Q') [Epi π'] (e₀ : M' ≅ (Scheme.Modules.pullback k).obj M)
    (e₁ : Q' ≅ (Scheme.Modules.pullback k).obj Q)
    (hπ : π' ≫ e₁.hom = e₀.hom ≫ (Scheme.Modules.pullback k).map π) {m : ℕ} (F : Flag Q m) :
    Flag.comap π' (Flag.pullback k e₁ F) = Flag.pullback k e₀ (Flag.comap π F) := by
  refine Flag.ext (funext fun i => ?_)
  set S := F.sub i
  have hS : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (cokernel S.arrow) (i + 1) := F.rank i
  have hCS : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (cokernel (comapSub π S).arrow) (i + 1) := (rank_comapSub_iff π S _).mpr hS
  show comapSub π' (have := mono_pullback_map_arrow k S _ hS;
      Subobject.mk ((Scheme.Modules.pullback k).map S.arrow ≫ e₁.inv)) =
    (have := mono_pullback_map_arrow k (comapSub π S) _ hCS;
      Subobject.mk ((Scheme.Modules.pullback k).map (comapSub π S).arrow ≫ e₀.inv))
  rw [mk_pullback_arrow_eq_kernelSubobject k e₁ S _ hS,
    mk_pullback_arrow_eq_kernelSubobject k e₀ (comapSub π S) _ hCS]
  set S' := kernelSubobject (e₁.hom ≫ (Scheme.Modules.pullback k).map (cokernel.π S.arrow))
  obtain ⟨α, hα⟩ := exists_iso_of_kernelSubobject_eq (cokernel.π S'.arrow)
    (e₁.hom ≫ (Scheme.Modules.pullback k).map (cokernel.π S.arrow)) (kernelSubobject_cokernel_π S')
  obtain ⟨β, hβ⟩ := exists_iso_of_kernelSubobject_eq (cokernel.π (comapSub π S).arrow)
    (π ≫ cokernel.π S.arrow) (kernelSubobject_cokernel_π _)
  exact (kernelSubobject_eq_of_comp_eq α.hom (p' := (e₀.hom ≫ (Scheme.Modules.pullback k).map
          (cokernel.π (comapSub π S).arrow)) ≫ (Scheme.Modules.pullback k).map β.hom)
        (by rw [Category.assoc, hα, reassoc_of% hπ, Category.assoc,
          ← CategoryTheory.Functor.map_comp, ← hβ, CategoryTheory.Functor.map_comp])).trans
    (kernelSubobject_comp_mono _ _)

end ComapPullback

/-! ### The Grassmannian over `X` -/

section Grassmannian

open AlgebraicGeometry.Grassmannian

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

variable (l n : ℕ)

/-- **Morphisms into the Grassmannian are its points**: a morphism `T ⟶ G(l, n)` is an
isomorphism class of rank `n - l` quotients of `𝒪_T^n` (the representability of 089S). -/
def grassmannianPointsEquiv (T : Scheme.{u}) : (T ⟶ scheme.{u} l n) ≃ Points T l n :=
  (schemeRepresentableBy l n).homEquiv.trans ((functorData l n).objEquiv T)

/-- The identification is natural: precomposition is pullback of presentations. -/
theorem grassmannianPointsEquiv_comp {T T' : Scheme.{u}} (k : T' ⟶ T) (g : T ⟶ scheme.{u} l n) :
    grassmannianPointsEquiv l n T' (k ≫ g) =
      pullbackPointsMap k l n (grassmannianPointsEquiv l n T g) := by
  show (functorData l n).objEquiv T' ((schemeRepresentableBy l n).homEquiv (k ≫ g)) =
    pullbackPointsMap k l n ((functorData l n).objEquiv T ((schemeRepresentableBy l n).homEquiv g))
  rw [Functor.RepresentableBy.homEquiv_comp]
  generalize (schemeRepresentableBy l n).homEquiv g = x
  obtain ⟨q, hq⟩ := Quotient.exists_rep ((functorData l n).objEquiv T x)
  have hx : x = ((functorData l n).objEquiv T).symm (Quotient.mk _ q) := by
    rw [hq]
    exact (Equiv.symm_apply_apply _ _).symm
  obtain ⟨q', hq', e, he⟩ := (functorData l n).map_isPullback k q
  rw [hx, Equiv.apply_symm_apply]
  show _ = Quotient.mk _ (pullbackPresentation k q)
  refine hq'.trans (Quotient.sound (Relation.EqvGen.rel _ _ ⟨e.symm, ?_⟩))
  show q'.map ≫ e.inv = (pullbackFreeIso k n).inv ≫ (Scheme.Modules.pullback k).map q.map
  have h1 : (Scheme.Modules.pullback k).map q.map = (pullbackFreeIso k n).hom ≫ q'.map ≫ e.inv := by
    have h := congrArg (fun t => t ≫ e.inv) he
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
    exact h.trans (Category.assoc _ _ _)
  simp only [h1, Iso.inv_hom_id_assoc]
  rfl

/-- The universal point: the class of the identity of `G(l, n)`. -/
def universalPoint : Points (scheme.{u} l n) l n :=
  grassmannianPointsEquiv l n _ (𝟙 _)

/-- A presentation representing the universal point. -/
def universalPresentation : QuotientPresentation (scheme.{u} l n) l n :=
  Quotient.out (universalPoint l n)

/-- **Every point is a pullback of the universal one.** -/
theorem grassmannianPointsEquiv_eq {T : Scheme.{u}} (g : T ⟶ scheme.{u} l n) :
    grassmannianPointsEquiv l n T g =
      Quotient.mk (quotientPresentationSetoid T l n)
        (pullbackPresentation g (universalPresentation l n)) := by
  conv_lhs => rw [← Category.comp_id g]
  rw [grassmannianPointsEquiv_comp]
  show pullbackPointsMap g l n (universalPoint l n) = _
  rw [← Quotient.out_eq (universalPoint l n)]
  rfl

/-- `QuotientPresentation.Isomorphic` is an equivalence relation. -/
theorem equivalence_isomorphic (T : Scheme.{u}) :
    Equivalence (QuotientPresentation.Isomorphic (X := T) (k := l) (n := n)) where
  refl _ := ⟨Iso.refl _, Category.comp_id _⟩
  symm := fun {x _} ⟨e, he⟩ => ⟨e.symm, (congrArg (· ≫ e.inv) he.symm).trans
    ((Category.assoc _ _ _).trans ((congrArg (x.map ≫ ·) e.hom_inv_id).trans
      (Category.comp_id _)))⟩
  trans := fun ⟨e, he⟩ ⟨e', he'⟩ => ⟨e ≪≫ e', (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ e'.hom) he).trans he')⟩

/-- Two presentations with the same class are isomorphic. -/
theorem isomorphic_of_mk_eq {T : Scheme.{u}} {q q' : QuotientPresentation T l n}
    (h : Quotient.mk (quotientPresentationSetoid T l n) q =
      Quotient.mk (quotientPresentationSetoid T l n) q') : q.Isomorphic q' :=
  (equivalence_isomorphic l n T).eqvGen_iff.mp (Quotient.exact h)

variable (X : Scheme.{u})

/-- **The universal quotient on `G(l, n)_X`**: the pullback along `G(l, n)_X ⟶ G(l, n)` of the
universal presentation, a surjection `𝒪^n ↠ 𝒬` onto a module of rank `n - l`. -/
def universalQuotient : QuotientPresentation (schemeOver.{u} l n X) l n :=
  pullbackPresentation (pullback.snd _ _) (universalPresentation l n)

/-- The point of `G(l, n)` classified by the pullback of the universal quotient along
`h : T ⟶ G(l, n)_X` is the second projection of `h`. -/
theorem mk_pullbackPresentation_universalQuotient {T : Scheme.{u}} (h : T ⟶ schemeOver.{u} l n X) :
    Quotient.mk (quotientPresentationSetoid T l n)
        (pullbackPresentation h (universalQuotient l n X)) =
      grassmannianPointsEquiv l n T (h ≫ pullback.snd _ _) := by
  rw [grassmannianPointsEquiv_eq]
  show _ = pullbackPointsMap (h ≫ pullback.snd _ _) l n
    (Quotient.mk (quotientPresentationSetoid _ l n) (universalPresentation l n))
  rw [pullbackPointsMap_comp]
  rfl

variable {X} in
/-- **The points of `G(l, n)_X` over `f : T ⟶ X`** are the morphisms `T ⟶ G(l, n)`. -/
def grassmannianOverEquiv {T : Scheme.{u}} (f : T ⟶ X) :
    { h : T ⟶ schemeOver.{u} l n X // h ≫ pullback.fst _ _ = f } ≃ (T ⟶ scheme.{u} l n) where
  toFun h := h.1 ≫ pullback.snd _ _
  invFun g := ⟨pullback.lift f g (terminal.hom_ext _ _), pullback.lift_fst _ _ _⟩
  left_inv h := Subtype.ext (pullback.hom_ext ((pullback.lift_fst _ _ _).trans h.2.symm)
    (pullback.lift_snd _ _ _))
  right_inv _ := pullback.lift_snd _ _ _

/-- The free module `𝒪_X^n`. -/
abbrev freeModule : X.Modules :=
  _root_.SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))

/-- The free module `𝒪_X^n` is finite locally free of rank `n`. -/
theorem rank_freeModule :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (freeModule n X) n :=
  AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_free (R := X.ringCatSheaf) n

/-- The free module `𝒪_X^n` is finite locally free. -/
theorem isFiniteLocallyFree_freeModule :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (freeModule n X) :=
  @AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ _ _ _ _ _ _ n
    (rank_freeModule n X)

/-- The universal quotient `𝒬` on `G(l, n)_X` is finite locally free of rank `n - l`. -/
theorem rank_universalQuotient :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (universalQuotient l n X).target (n - l) :=
  (universalQuotient l n X).finiteLocallyFree

/-- The universal quotient `𝒬` on `G(l, n)_X` is finite locally free. -/
theorem isFiniteLocallyFree_universalQuotient :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (universalQuotient l n X).target :=
  @AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ _ _ _ _ _ _
    (n - l) (rank_universalQuotient l n X)

/-- **Tower B over `X`**: the partial flag variety built on `𝒪_X^n`, of length `n - l`. -/
abbrev towerB : Σ Y : Scheme.{u}, Y ⟶ X :=
  @tower (n - l) X (freeModule n X) (isFiniteLocallyFree_freeModule n X)

/-- **Tower A over `G(l, n)_X`**: the partial flag variety built on the universal quotient, of
length `n - l`. -/
abbrev towerA : Σ Y : Scheme.{u}, Y ⟶ schemeOver.{u} l n X :=
  @tower (n - l) _ (universalQuotient l n X).target (isFiniteLocallyFree_universalQuotient l n X)

/-- The structure morphism of tower A to `X`, through `G(l, n)_X ⟶ X`. -/
abbrev towerAProj : (towerA l n X).1 ⟶ X :=
  (towerA l n X).2 ≫ pullback.fst _ _

variable {X}

/-- The identification `f^*𝒪_X^n ≅ 𝒪_T^n`, as an isomorphism of `𝒪_T`-modules. -/
def freeIso {T : Scheme.{u}} (f : T ⟶ X) :
    (Scheme.Modules.pullback f).obj (freeModule n X) ≅ freeModule n T :=
  pullbackFreeIso f n

/-- The quotient `𝒪_T^n ↠ h^*𝒬` that `h : T ⟶ G(l, n)_X` pulls back from the universal one. -/
def univMap {T : Scheme.{u}} (h : T ⟶ schemeOver.{u} l n X) :
    freeModule n T ⟶ (Scheme.Modules.pullback h).obj (universalQuotient l n X).target :=
  (pullbackPresentation h (universalQuotient l n X)).map

/-- The quotient `𝒪_T^n ⟶ h^*𝒬` is an epimorphism. -/
instance epi_univMap {T : Scheme.{u}} (h : T ⟶ schemeOver.{u} l n X) : Epi (univMap l n h) :=
  (pullbackPresentation h (universalQuotient l n X)).map_epi

/-- The quotient map `f^*𝒪_X^n ≅ 𝒪_T^n ↠ h^*𝒬` attached to a point `h` of `G(l, n)_X`. -/
def presMap {T : Scheme.{u}} (f : T ⟶ X) (h : T ⟶ schemeOver.{u} l n X) :
    (Scheme.Modules.pullback f).obj (freeModule n X) ⟶
      (Scheme.Modules.pullback h).obj (universalQuotient l n X).target :=
  (freeIso n f).hom ≫ univMap l n h

/-- The quotient map `f^*𝒪_X^n ⟶ h^*𝒬` is an epimorphism. -/
instance epi_presMap {T : Scheme.{u}} (f : T ⟶ X) (h : T ⟶ schemeOver.{u} l n X) :
    Epi (presMap l n f h) :=
  epi_comp _ _

/-- The pulled back universal quotient has rank `n - l`. -/
theorem rank_pullback_universalQuotient {T : Scheme.{u}} (h : T ⟶ schemeOver.{u} l n X) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback h).obj (universalQuotient l n X).target) (n - l) :=
  @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ h _ _ (rank_universalQuotient l n X)

/-- **The comparison of the two descriptions of the points.** For `f : T ⟶ X` and `l < n`, a
point `h` of `G(l, n)_X` over `f` with a flag of length `n - l` of `h^*𝒬` is the same datum as
a flag of length `n - l` of `f^*𝒪^n`, by pulling the flag back along `f^*𝒪^n ↠ h^*𝒬`. -/
def compareEquiv (hln : l < n) {T : Scheme.{u}} (f : T ⟶ X) :
    (Σ h : { h : T ⟶ schemeOver.{u} l n X // h ≫ pullback.fst _ _ = f },
      Flag ((Scheme.Modules.pullback h.1).obj (universalQuotient l n X).target) (n - l)) ≃
      Flag ((Scheme.Modules.pullback f).obj (freeModule n X)) (n - l) :=
  Equiv.ofBijective (fun x => Flag.comap (presMap l n f x.1.1) x.2) (by
    let i₀ : Fin (n - l) := ⟨n - l - 1, by omega⟩
    have hi₀ : (i₀ : ℕ) + 1 = n - l := by
      simp only [i₀]
      omega
    constructor
    · rintro ⟨h, F⟩ ⟨h', F'⟩ hFF
      have hbot : ∀ (h : { h : T ⟶ schemeOver.{u} l n X // h ≫ pullback.fst _ _ = f })
          (F : Flag ((Scheme.Modules.pullback h.1).obj (universalQuotient l n X).target) (n - l)),
          (Flag.comap (presMap l n f h.1) F).sub i₀ = kernelSubobject (presMap l n f h.1) := by
        intro h F
        have hF := F.rank i₀
        rw [hi₀] at hF
        rw [Flag.comap_sub, eq_bot_of_rank (S := F.sub i₀) (n - l)
          (rank_pullback_universalQuotient l n h.1) hF, comapSub_bot]
      have hker : kernelSubobject (presMap l n f h.1) = kernelSubobject (presMap l n f h'.1) := by
        rw [← hbot h F, ← hbot h' F']
        exact congrArg (fun G : Flag _ (n - l) => G.sub i₀) hFF
      obtain ⟨α, hα⟩ := exists_iso_of_kernelSubobject_eq _ _ hker
      have hα' : univMap l n h.1 ≫ α.hom = univMap l n h'.1 := by
        rw [← cancel_epi (freeIso n f).hom]
        simpa [presMap] using hα
      have hpt : grassmannianPointsEquiv l n T (h.1 ≫ pullback.snd _ _) =
          grassmannianPointsEquiv l n T (h'.1 ≫ pullback.snd _ _) := by
        rw [← mk_pullbackPresentation_universalQuotient,
          ← mk_pullbackPresentation_universalQuotient]
        exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨α, hα'⟩)
      have hh : h = h' := (grassmannianOverEquiv l n f).injective
        ((grassmannianPointsEquiv l n T).injective hpt)
      subst hh
      exact Sigma.ext rfl (heq_of_eq (Flag.comap_injective _ hFF))
    · intro K
      let K₀ := K.sub i₀
      have hK₀ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          (cokernel K₀.arrow) (n - l) := by
        have h := K.rank i₀
        rwa [hi₀] at h
      let p : QuotientPresentation T l n :=
        { target := cokernel K₀.arrow
          map := (freeIso n f).inv ≫ cokernel.π K₀.arrow
          map_epi := (epi_comp _ _ : Epi ((freeIso n f).inv ≫ cokernel.π K₀.arrow))
          finiteLocallyFree := hK₀ }
      let h := (grassmannianOverEquiv l n f).symm
        ((grassmannianPointsEquiv l n T).symm (Quotient.mk _ p))
      have hpt : Quotient.mk (quotientPresentationSetoid T l n)
          (pullbackPresentation h.1 (universalQuotient l n X)) = Quotient.mk _ p := by
        rw [mk_pullbackPresentation_universalQuotient]
        change grassmannianPointsEquiv l n T ((grassmannianOverEquiv l n f) h) = _
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      obtain ⟨e₀, he₀⟩ := isomorphic_of_mk_eq l n hpt
      let e : (Scheme.Modules.pullback h.1).obj (universalQuotient l n X).target ≅
          cokernel K₀.arrow := ⟨e₀.hom, e₀.inv, e₀.hom_inv_id, e₀.inv_hom_id⟩
      have he : univMap l n h.1 ≫ e.hom = (freeIso n f).inv ≫ cokernel.π K₀.arrow := he₀
      have hker : kernelSubobject (presMap l n f h.1) = K₀ :=
        calc kernelSubobject (presMap l n f h.1)
            = kernelSubobject (presMap l n f h.1 ≫ e.hom) := (kernelSubobject_comp_mono _ _).symm
          _ = kernelSubobject (cokernel.π K₀.arrow) :=
              kernelSubobject_congr (by rw [presMap, Category.assoc, he, Iso.hom_inv_id_assoc])
          _ = K₀ := kernelSubobject_cokernel_π K₀
      have hle : ∀ i, kernelSubobject (presMap l n f h.1) ≤ K.sub i := fun i =>
        hker ▸ K.antitone (Fin.le_iff_val_le_val.mpr (by simp only [i₀]; omega))
      choose S hS using fun i => exists_comapSub_eq (presMap l n f h.1) (hle i)
      refine ⟨⟨h, ⟨S, fun a b hab => ?_, fun i => ?_⟩⟩, Flag.ext (funext hS)⟩
      · exact (comapSub_le_comapSub_iff (presMap l n f h.1)).mp
          ((hS b).trans_le ((K.antitone hab).trans_eq (hS a).symm))
      · exact (rank_comapSub_iff (presMap l n f h.1) _ _).mp ((hS i) ▸ K.rank i))

/-- The comparison pulls the flag back along `f^*𝒪^n ↠ h^*𝒬`. -/
@[simp]
theorem compareEquiv_apply (hln : l < n) {T : Scheme.{u}} (f : T ⟶ X)
    (x : Σ h : { h : T ⟶ schemeOver.{u} l n X // h ≫ pullback.fst _ _ = f },
      Flag ((Scheme.Modules.pullback h.1).obj (universalQuotient l n X).target) (n - l)) :
    compareEquiv l n hln f x = Flag.comap (presMap l n f x.1.1) x.2 :=
  rfl

/-- The quotient `𝒪_T^n ⟶ h^*𝒬` is the inverse of `h^*𝒪^n ≅ 𝒪_T^n` followed by the pullback
of the universal quotient map. -/
theorem univMap_eq {T : Scheme.{u}} (h : T ⟶ schemeOver.{u} l n X) :
    univMap l n h =
      (freeIso n h).inv ≫ (Scheme.Modules.pullback h).map (universalQuotient l n X).map :=
  rfl

/-- The identifications `f^*𝒪^n ≅ 𝒪^n` are compatible with composition. -/
theorem freeIso_comp_inv {Y T T' : Scheme.{u}} (f : T ⟶ Y) (k : T' ⟶ T) :
    (freeIso n k).inv ≫ (Scheme.Modules.pullback k).map (freeIso n f).inv ≫
        (Scheme.Modules.pullbackComp k f).hom.app (freeModule n Y) =
      (freeIso n (k ≫ f)).inv :=
  pullbackFreeIso_comp_inv f k n

/-- **The quotient maps attached to points of `G(l, n)_X` are compatible with base change.** -/
theorem presMap_comp {T T' : Scheme.{u}} (k : T' ⟶ T) (f : T ⟶ X)
    (h : T ⟶ schemeOver.{u} l n X) (f' : T' ⟶ X) (hf' : k ≫ f = f')
    (h' : T' ⟶ schemeOver.{u} l n X) (hc : k ≫ h = h') :
    presMap l n f' h' ≫ (((Scheme.Modules.pullbackComp k h).app _ ≪≫
        (Scheme.Modules.pullbackCongr hc).app _).symm).hom =
      (((Scheme.Modules.pullbackComp k f).app _ ≪≫
        (Scheme.Modules.pullbackCongr hf').app _).symm).hom ≫
        (Scheme.Modules.pullback k).map (presMap l n f h) := by
  subst hc hf'
  have e1 := freeIso_comp_inv n h k
  have e2 := freeIso_comp_inv n f k
  have n1 := (Scheme.Modules.pullbackComp k h).inv.naturality (universalQuotient l n X).map
  have a1 : (freeIso n (k ≫ h)).inv ≫ (Scheme.Modules.pullbackComp k h).inv.app _ =
      (freeIso n k).inv ≫ (Scheme.Modules.pullback k).map (freeIso n h).inv := by
    rw [← e1]
    simp
  have a2 : (freeIso n (k ≫ f)).hom = (Scheme.Modules.pullbackComp k f).inv.app _ ≫
      (Scheme.Modules.pullback k).map (freeIso n f).hom ≫ (freeIso n k).hom := by
    rw [← cancel_mono (freeIso n (k ≫ f)).inv, Iso.hom_inv_id, ← e2]
    simp
  simp only [presMap, univMap_eq, Iso.symm_hom, Iso.trans_inv, Iso.app_inv,
    Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv, NatTrans.id_app, Category.assoc,
    Category.id_comp, CategoryTheory.Functor.map_comp]
  rw [n1, reassoc_of% a1, a2]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rfl

variable (X)

/-- **The points of tower A over `X`**: a point `h` of `G(l, n)_X` over `f` and a flag of
`h^*𝒬` of length `n - l`. -/
def towerAEquiv {T : Scheme.{u}} (f : T ⟶ X) :
    { g : T ⟶ (towerA l n X).1 // g ≫ towerAProj l n X = f } ≃
      Σ h : { h : T ⟶ schemeOver.{u} l n X // h ≫ pullback.fst _ _ = f },
        Flag ((Scheme.Modules.pullback h.1).obj (universalQuotient l n X).target) (n - l) :=
  (overCompEquiv (Y := (towerA l n X).1) (P := schemeOver.{u} l n X) (towerA l n X).2
      (pullback.fst _ _) f).trans
    (Equiv.sigmaCongrRight fun h =>
      @towerEquiv (n - l) _ (universalQuotient l n X).target
        (isFiniteLocallyFree_universalQuotient l n X) _ h.1)

/-- **The points of tower B over `X`**: the flags of `f^*𝒪^n` of length `n - l`. -/
def towerBEquiv {T : Scheme.{u}} (f : T ⟶ X) :
    { g : T ⟶ (towerB l n X).1 // g ≫ (towerB l n X).2 = f } ≃
      Flag ((Scheme.Modules.pullback f).obj (freeModule n X)) (n - l) :=
  @towerEquiv (n - l) X (freeModule n X) (isFiniteLocallyFree_freeModule n X) _ f

variable (hln : l < n)

/-- **The two towers have the same points over `X`.** -/
def towerPointsEquiv {T : Scheme.{u}} (f : T ⟶ X) :
    { g : T ⟶ (towerA l n X).1 // g ≫ towerAProj l n X = f } ≃
      { g : T ⟶ (towerB l n X).1 // g ≫ (towerB l n X).2 = f } :=
  (towerAEquiv l n X f).trans ((compareEquiv l n hln f).trans (towerBEquiv l n X f).symm)

/-- **The identification of the points is natural in the test scheme.** -/
theorem towerPointsEquiv_comp {T T' : Scheme.{u}} (k : T' ⟶ T) (f : T ⟶ X)
    (g : { g : T ⟶ (towerA l n X).1 // g ≫ towerAProj l n X = f }) (f' : T' ⟶ X)
    (hf' : k ≫ f = f') :
    towerPointsEquiv l n X hln f' ⟨k ≫ g.1, by rw [Category.assoc, g.2, hf']⟩ =
      ⟨k ≫ (towerPointsEquiv l n X hln f g).1, by
        rw [Category.assoc, (towerPointsEquiv l n X hln f g).2, hf']⟩ := by
  apply (towerBEquiv l n X f').injective
  rw [towerPointsEquiv, Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [towerBEquiv, @towerEquiv_comp (n - l) X (freeModule n X) (isFiniteLocallyFree_freeModule n X)
    _ _ k f _ f' hf']
  show _ = Flag.pullback k _ ((towerBEquiv l n X f) ((towerBEquiv l n X f).symm
    (compareEquiv l n hln f (towerAEquiv l n X f g))))
  rw [Equiv.apply_symm_apply]
  set h := g.1 ≫ (towerA l n X).2 with hh
  have hc : k ≫ h = (k ≫ g.1) ≫ (towerA l n X).2 := (Category.assoc _ _ _).symm
  have hA := @towerEquiv_comp (n - l) _ (universalQuotient l n X).target
    (isFiniteLocallyFree_universalQuotient l n X) _ _ k h ⟨g.1, rfl⟩ _ hc
  show Flag.comap (presMap l n f' ((k ≫ g.1) ≫ (towerA l n X).2))
      (@towerEquiv (n - l) _ (universalQuotient l n X).target
        (isFiniteLocallyFree_universalQuotient l n X) _ ((k ≫ g.1) ≫ (towerA l n X).2)
        ⟨k ≫ g.1, rfl⟩) =
    Flag.pullback k _ (Flag.comap (presMap l n f h)
      (@towerEquiv (n - l) _ (universalQuotient l n X).target
        (isFiniteLocallyFree_universalQuotient l n X) _ h ⟨g.1, rfl⟩))
  rw [hA]
  exact Flag.comap_pullback k _ _ _ _ (presMap_comp l n k f h f' hf' _ hc) _

/-- The morphism from tower A to tower B over `X`: the image of the identity of tower A. -/
def flagTowerHom : (towerA l n X).1 ⟶ (towerB l n X).1 :=
  (towerPointsEquiv l n X hln (towerAProj l n X) ⟨𝟙 _, Category.id_comp _⟩).1

/-- The morphism from tower B to tower A over `X`: the preimage of the identity of tower B. -/
def flagTowerInv : (towerB l n X).1 ⟶ (towerA l n X).1 :=
  ((towerPointsEquiv l n X hln (towerB l n X).2).symm ⟨𝟙 _, Category.id_comp _⟩).1

/-- The morphism from tower A to tower B is a morphism over `X`. -/
theorem flagTowerHom_comp : flagTowerHom l n X hln ≫ (towerB l n X).2 = towerAProj l n X :=
  (towerPointsEquiv l n X hln _ _).2

/-- The morphism from tower B to tower A is a morphism over `X`. -/
theorem flagTowerInv_comp : flagTowerInv l n X hln ≫ towerAProj l n X = (towerB l n X).2 :=
  ((towerPointsEquiv l n X hln _).symm _).2

/-- **The partial flag variety, as a tower of projective bundles over `X × G(l, n)` and as one
over `X`, is the same scheme over `X`.** For `l < n`, tower A
(`Stacks.FlagTower.tower (n - l) 𝒬` over `G(l, n)_X = X ×_{Spec ℤ} G(l, n)`, built on the
universal quotient) and tower B (`Stacks.FlagTower.tower (n - l) 𝒪_X^n` over `X`) are
isomorphic, compatibly with their structure morphisms to `X`
(`Stacks.FlagTower.flagTowerIso_hom_comp`). -/
def flagTowerIso : (towerA l n X).1 ≅ (towerB l n X).1 where
  hom := flagTowerHom l n X hln
  inv := flagTowerInv l n X hln
  hom_inv_id := by
    have key := towerPointsEquiv_comp l n X hln (flagTowerHom l n X hln) (towerB l n X).2
      ((towerPointsEquiv l n X hln (towerB l n X).2).symm ⟨𝟙 _, Category.id_comp _⟩)
      (towerAProj l n X) (flagTowerHom_comp l n X hln)
    have hv := congrArg Subtype.val key
    simp only [Equiv.apply_symm_apply, Category.comp_id] at hv
    have hinj := (towerPointsEquiv l n X hln (towerAProj l n X)).injective
      (Subtype.ext hv : towerPointsEquiv l n X hln (towerAProj l n X) ⟨_, _⟩ =
        towerPointsEquiv l n X hln (towerAProj l n X) ⟨𝟙 _, Category.id_comp _⟩)
    exact congrArg Subtype.val hinj
  inv_hom_id := by
    have key := towerPointsEquiv_comp l n X hln (flagTowerInv l n X hln) (towerAProj l n X)
      ⟨𝟙 _, Category.id_comp _⟩ (towerB l n X).2 (flagTowerInv_comp l n X hln)
    have hl : (⟨flagTowerInv l n X hln ≫ 𝟙 _, by rw [Category.comp_id, flagTowerInv_comp]⟩ :
        { g : _ ⟶ (towerA l n X).1 // g ≫ towerAProj l n X = (towerB l n X).2 }) =
        (towerPointsEquiv l n X hln (towerB l n X).2).symm ⟨𝟙 _, Category.id_comp _⟩ :=
      Subtype.ext (Category.comp_id _)
    simp only [hl, Equiv.apply_symm_apply] at key
    exact (congrArg Subtype.val key).symm

/-- **The isomorphism is over `X`.** -/
@[reassoc (attr := simp)]
theorem flagTowerIso_hom_comp :
    (flagTowerIso l n X hln).hom ≫ (towerB l n X).2 = towerAProj l n X :=
  flagTowerHom_comp l n X hln

/-- The isomorphism of the two towers as objects over `X`. -/
def flagTowerOverIso : Over.mk (towerAProj l n X) ≅ Over.mk (towerB l n X).2 :=
  Over.isoMk (flagTowerIso l n X hln) (flagTowerIso_hom_comp l n X hln)

end Grassmannian

end Stacks.FlagTower

end
